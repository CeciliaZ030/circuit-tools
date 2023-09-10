//! Circuit utilities
use std::{
    collections::HashMap,
    marker::PhantomData,
    ops::{Add, Mul},
    vec,
};
use zkevm_circuits::table::LookupTable;
use crate::util::{rlc, query_expression, and, sum, Expr, Scalar};
use eth_types::{Field, Word};
use halo2_proofs::plonk::{ConstraintSystem, Expression, Column, Advice};
use itertools::Itertools;

use super::{
    cached_region::StoredExpression,
    cell_manager::{Cell, CellManager, CellType},
};

fn get_condition_expr<F: Field>(conditions: &Vec<Expression<F>>) -> Expression<F> {
    if conditions.is_empty() {
        1.expr()
    } else {
        and::expr(conditions)
    }
}

/// Table data
#[derive(Clone, Debug)]
pub struct TableData<F> {
    /// Desciption
    pub description: &'static str,
    /// Condition under which the lookup needs to be done
    pub regional_condition: Expression<F>,
    /// Need to store local condition for dyn table checks
    pub local_condition: Expression<F>,
    /// The values to lookup
    pub values: Vec<Expression<F>>,
    /// region
    pub region_id: usize,
}

/// Lookup data
#[derive(Clone, Debug)]
pub struct LookupData<F> {
    /// Desciption
    pub description: String,
    /// Condition under which the lookup needs to be done
    pub regional_condition: Expression<F>,
    /// Need to store local condition for dyn table checks
    pub local_condition: Expression<F>,
    /// The values to lookup
    pub values: Vec<Expression<F>>,
    /// The values to lookup
    pub table: Vec<Expression<F>>,
    /// region
    pub region_id: usize,
}

impl<F: Field> TableData<F> {
    fn condition(&self) -> Expression<F> {
        self.regional_condition.expr() * self.local_condition.expr()
    }
}

impl<F: Field> LookupData<F> {
    fn condition(&self) -> Expression<F> {
        self.regional_condition.expr() * self.local_condition.expr()
    }
}

struct TableMerger<F, C> {
    data: Vec<TableData<F>>,
    _phantom: PhantomData<C>,
}

impl<F: Field, C: CellType> TableMerger<F, C> {
    fn merge_check(&self, cb: &mut ConstraintBuilder<F, C>) {
        let selector = sum::expr(self.data.iter().map(|t| t.condition()));
        crate::circuit!([meta, cb], {
            require!(selector => bool);
        });
    }

    fn merge_unsafe(&self) -> (Expression<F>, Vec<Expression<F>>) {
        if self.data.is_empty() {
            return (0.expr(), Vec::new());
        }
        let selector = sum::expr(self.data.iter().map(|v| v.condition()));
        // Merge
        let max_length = self.data.iter().map(|t| t.values.len()).max().unwrap();
        let mut merged_values = vec![0.expr(); max_length];
        let default_value = 0.expr();
        merged_values.iter_mut().enumerate().for_each(|(idx, v)| {
            *v = sum::expr(
                self.data
                    .iter()
                    .map(|t| t.condition() * t.values.get(idx).unwrap_or(&default_value).expr()),
            );
        });
        (selector, merged_values)
    }

    fn check_and_merge(
        &self,
        cb: &mut ConstraintBuilder<F, C>,
    ) -> (Expression<F>, Vec<Expression<F>>) {
        self.merge_check(cb);
        self.merge_unsafe()
    }

    fn merge_and_select(&self, _cb: &mut ConstraintBuilder<F, C>) -> Vec<Expression<F>> {
        let (selector, v) = self.merge_unsafe();
        v.iter().map(|v| selector.expr() * v.expr()).collect()
    }
}

/// Constraint builder
#[derive(Clone)]
pub struct ConstraintBuilder<F, C: CellType> {
    /// Constraints to be returned to meta
    constraints: Vec<(&'static str, Expression<F>)>,
    /// Max global degree of constraints
    max_global_degree: usize,
    /// Max local degree of constraints inside the current region
    max_degree: usize,
    /// conditions for constraints
    conditions: Vec<Expression<F>>,
    /// Columns whoes equality constraints needed to be enable
    equalities: Vec<Column<Advice>>,
    /// The tables
    pub tables: HashMap<C::TableType, Vec<TableData<F>>>,
    /// Lookups
    pub lookups: Vec<LookupData<F>>,
    /// All stored expressions
    pub stored_expressions: HashMap<usize, Vec<StoredExpression<F, C>>>,
    /// CellManager
    pub cell_manager: Option<CellManager<F, C>>,
    /// Disable macro-generated description for constraints & lookups
    /// for graph display
    pub disable_description: bool,
    /// region id
    pub region_id: usize,
    /// lookup input challenge
    pub lookup_challenge: Option<Expression<F>>,
    /// state contect
    pub state_context: Vec<Expression<F>>,
    /// state constraints start
    pub region_constraints_start: usize,
}

impl<F: Field, C: CellType> ConstraintBuilder<F, C> {
    pub(crate) fn new(
        max_degree: usize,
        cell_manager: Option<CellManager<F, C>>,
        lookup_challenge: Option<Expression<F>>,
    ) -> Self {
        ConstraintBuilder {
            constraints: Vec::new(),
            max_global_degree: max_degree,
            max_degree,
            conditions: Vec::new(),
            equalities: Vec::new(),
            tables: HashMap::new(),
            lookups: Vec::new(),
            cell_manager,
            disable_description: false,
            stored_expressions: HashMap::new(),
            region_id: 0,
            lookup_challenge,
            state_context: Vec::new(),
            region_constraints_start: 0,
        }
    }

    pub(crate) fn restart(&mut self) {
        self.constraints.clear();
        self.conditions.clear();
        self.equalities.clear();
        self.tables.clear();
        self.lookups.clear();
        self.stored_expressions.clear();
        self.region_id = 0;
        self.state_context.clear();
        self.region_constraints_start = 0;
        if let Some(cell_manager) = &mut self.cell_manager {
            cell_manager.restart();
        }
    }

    pub(crate) fn set_cell_manager(&mut self, cell_manager: CellManager<F, C>) {
        self.cell_manager = Some(cell_manager);
    }

    pub(crate) fn set_max_degree(&mut self, max_degree: usize) {
        self.max_global_degree = max_degree;
    }

    pub(crate) fn push_region(&mut self, region_id: usize, height: usize) {
        assert!(region_id != 0);
        self.region_id = region_id;
        self.state_context = self.conditions.clone();
        self.max_degree = self.max_global_degree - self.get_condition_expr().degree();
        self.conditions.clear();
        self.region_constraints_start = self.constraints.len();

        // Simply resets the cell manager for now, so all previously allocated cells will be freed
        self.cell_manager.as_mut().unwrap().reset(height);
    }

    pub(crate) fn pop_region(&mut self) {
        // Apply the region condition to all contraints added in this region
        let condition = get_condition_expr(&self.state_context);
        for idx in self.region_constraints_start..self.constraints.len() {
            self.constraints[idx].1 = condition.expr() * self.constraints[idx].1.clone();
        }
        self.conditions = self.state_context.clone();
        self.max_degree = self.max_global_degree - self.get_condition_expr().degree();
        self.region_id = 0;
        self.state_context.clear();
    }

    pub(crate) fn set_disable_description(&mut self, disable_description: bool) {
        self.disable_description = disable_description;
    }

    pub(crate) fn require_zero(&mut self, name: &'static str, constraint: Expression<F>) {
        self.add_constraint(name, constraint);
    }

    pub(crate) fn require_equal(
        &mut self,
        name: &'static str,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) {
        self.add_constraint(name, lhs - rhs);
    }

    pub(crate) fn require_boolean(&mut self, name: &'static str, value: Expression<F>) {
        self.add_constraint(name, value.clone() * (1.expr() - value));
    }

    pub(crate) fn require_in_set(
        &mut self,
        name: &'static str,
        value: Expression<F>,
        set: Vec<Expression<F>>,
    ) {
        self.add_constraint(
            name,
            set.iter()
                .fold(1.expr(), |acc, item| acc * (value.clone() - item.clone())),
        );
    }

    pub(crate) fn enable_equality(&mut self, column: Column<Advice>){
        self.equalities.push(column);
    }

    pub(crate) fn condition<R>(
        &mut self,
        condition: Expression<F>,
        constraint: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.push_condition(condition);
        let ret = constraint(self);
        self.pop_condition();
        ret
    }

    pub(crate) fn push_condition(&mut self, condition: Expression<F>) {
        self.conditions.push(condition);
    }

    pub(crate) fn pop_condition(&mut self) {
        self.conditions.pop();
    }

    pub(crate) fn add_constraints(&mut self, constraints: Vec<(&'static str, Expression<F>)>) {
        for (name, constraint) in constraints {
            self.add_constraint(name, constraint);
        }
    }

    pub(crate) fn add_constraint(&mut self, name: &'static str, constraint: Expression<F>) {
        if self.max_global_degree == 0 {
            return;
        }
        let constraint = match self.get_condition() {
            Some(condition) => condition * constraint,
            None => constraint,
        };
        let constraint = self.split_expression(name, constraint);
        self.validate_degree(constraint.degree(), name);
        self.constraints.push((name, constraint));
    }

    pub(crate) fn get_condition(&self) -> Option<Expression<F>> {
        if self.conditions.is_empty() {
            None
        } else {
            Some(and::expr(self.conditions.iter()))
        }
    }

    pub(crate) fn get_condition_expr(&self) -> Expression<F> {
        self.get_condition().unwrap_or_else(|| 1.expr())
    }

    // Query

    pub(crate) fn query_bool(&mut self) -> Cell<F> {
        let cell = self.query_default();
        self.require_boolean("Constrain cell to be a bool", cell.expr());
        cell
    }

    pub(crate) fn query_default(&mut self) -> Cell<F> {
        self.query_cells_dyn(C::default(), 1)
            .get(0)
            .expect("No cell found")
            .clone()
    }

    pub(crate) fn query_one(&mut self, cell_type: C) -> Cell<F> {
        self.query_cells_dyn(cell_type, 1).first().unwrap().clone()
    }

    pub(crate) fn query_bytes<const N: usize>(&mut self) -> [Cell<F>; N] {
        self.query_cells_dyn(
            C::byte_type().expect("No byte type for this CellManager"),
            N,
        )
        .try_into()
        .unwrap()
    }

    pub(crate) fn query_cells_dyn(&mut self, cell_type: C, count: usize) -> Vec<Cell<F>> {
        self.cell_manager
            .as_mut()
            .expect("Cell manager not set")
            .query_cells(cell_type, count)
    }

    pub(crate) fn query_cell_with_type(&mut self, cell_type: C) -> Cell<F> {
        self.query_cells_dyn(cell_type, 1).first().unwrap().clone()
    }

    pub(crate) fn validate_degree(&self, degree: usize, name: &'static str) {
        if self.max_global_degree > 0 && self.region_id != 0 {
            debug_assert!(
                degree <= self.max_degree,
                "Expression {} degree too high: {} > {}",
                name,
                degree,
                self.max_degree,
            );
        }
    }

    pub(crate) fn build_constraints(&self) -> Vec<(&'static str, Expression<F>)> {
        if self.constraints.is_empty() {
            return vec![("No constraints", 0.expr())];
        }
        self.constraints.clone()
    }

    pub(crate) fn build_equalities(&self, meta: &mut ConstraintSystem<F>) {
        self.equalities
            .iter()
            .for_each(|c| {
                meta.enable_equality(c.clone())}
            );
    }
    
    pub(crate) fn build_lookups(&mut self, meta: &mut ConstraintSystem<F>) {
        for lookup in self.lookups.iter() {
            let mut values: Vec<_> = lookup
                .values
                .iter()
                .map(|value| value.expr() * lookup.condition())
                .collect();
            // Align the length of values and table
            assert!(lookup.table.len() >= values.len());
            while values.len() < lookup.table.len() {
                values.push(0.expr());
            }
            meta.lookup_any(
                Box::leak(lookup.description.clone().into_boxed_str()),
                |_meta| {
                    values
                        .iter()
                        .zip(lookup.table.iter())
                        .map(|(v, t)| (v.expr(), t.expr()))
                        .collect()
                },
            );
        }
    }

    pub(crate) fn store_tuple(
        &mut self,
        description: &'static str,
        cell_type: C,
        values: Vec<Expression<F>>,
    ) -> Expression<F> {
        let challenge = self.lookup_challenge.clone().unwrap();
        let rlc = rlc::expr(&values, challenge.expr()) * self.get_condition_expr();
        let reduced_rlc = self.split_expression("compression", rlc);
        self.store_expression(description, reduced_rlc, cell_type, None)
    }

    /// Store the table as is without taking into account any active conditions
    pub(crate) fn load_table(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        table_type: C::TableType,
        table: &dyn LookupTable<F>,
    ) {
        query_expression(meta, |meta| {
            let description = format!("{:?}", table_type);
            self.store_table_with_condition(
                Box::leak(description.into_boxed_str()),
                table_type,
                table.table_exprs(meta),
                1.expr(),
                1.expr(),
            );
        });
    }

    /// Store the table taking into account the current active conditions
    pub(crate) fn store_table(
        &mut self,
        description: &'static str,
        table_type: C::TableType,
        values: Vec<Expression<F>>,
    ) {
        self.store_table_with_condition(
            description,
            table_type,
            values,
            self.get_condition_expr(),
            get_condition_expr(&self.state_context),
        );
    }

    pub(crate) fn store_table_with_condition(
        &mut self,
        description: &'static str,
        table_type: C::TableType,
        values: Vec<Expression<F>>,
        local_condition: Expression<F>,
        regional_condition: Expression<F>,
    ) {
        let data = TableData {
            description,
            local_condition,
            regional_condition,
            values,
            region_id: self.region_id,
        };
        if let Some(tables) = self.tables.get_mut(&table_type) {
            tables.push(data);
        } else {
            self.tables.insert(table_type, vec![data]);
        }
    }

    pub(crate) fn table(&self, table_type: C::TableType) -> Vec<Expression<F>> {
        let tables = self.tables.get(&table_type).unwrap();
        assert!(tables.len() == 1);
        tables[0].values.clone()
    }

    pub(crate) fn add_lookup(
        &mut self,
        description: String,
        values: Vec<Expression<F>>,
        table: Vec<Expression<F>>,
    ) {
        let data = LookupData {
            description,
            local_condition: self.get_condition_expr(),
            regional_condition: get_condition_expr(&self.state_context),
            values,
            table,
            region_id: self.region_id,
        };
        self.lookups.push(data);
    }

    pub(crate) fn dynamic_table_merged(&mut self, tag: C::TableType) -> Vec<Expression<F>> {
        let data = self
            .tables
            .get(&tag)
            .unwrap_or_else(|| panic!("Dynamic table {:?} not found", tag))
            .clone();
        let table_merger = TableMerger {
            data,
            _phantom: PhantomData,
        };
        table_merger.merge_and_select(self)
    }

    pub(crate) fn store_expression(
        &mut self,
        name: &str,
        expr: Expression<F>,
        cell_type: C,
        target_cell: Option<Cell<F>>,
    ) -> Expression<F> {
        // Check if we already stored the expression somewhere
        let stored_expression = self.find_stored_expression(&expr, cell_type);
        match stored_expression {
            Some(stored_expression) => stored_expression.cell.expr(),
            None => {
                // Require the stored value to equal the value of the expression
                let cell = if let Some(tc) = target_cell {
                    tc
                } else {
                    self.query_one(cell_type)
                };
                let name = format!("{} (stored expression)", name);
                self.constraints.push((
                    Box::leak(name.clone().into_boxed_str()),
                    cell.expr() - expr.clone(),
                ));
                self.stored_expressions
                    .entry(self.region_id)
                    .or_insert_with(Vec::new)
                    .push(StoredExpression {
                        name,
                        cell: cell.clone(),
                        cell_type,
                        expr_id: expr.identifier(),
                        expr,
                    });
                cell.expr()
            }
        }
    }

    pub(crate) fn get_stored_expressions(&self, region_id: usize) -> Vec<StoredExpression<F, C>> {
        self.stored_expressions
            .get(&region_id)
            .cloned()
            .unwrap_or_default()
    }

    pub(crate) fn find_stored_expression(
        &self,
        expr: &Expression<F>,
        cell_type: C,
    ) -> Option<&StoredExpression<F, C>> {
        let expr_id = expr.identifier();
        if let Some(stored_expressions) = self.stored_expressions.get(&self.region_id) {
            stored_expressions
                .iter()
                .find(|&e| e.cell_type == cell_type && e.expr_id == expr_id)
        } else {
            None
        }
    }

    pub(crate) fn split_expression(
        &mut self,
        name: &'static str,
        expr: Expression<F>,
    ) -> Expression<F> {
        if expr.degree() > self.max_degree && self.region_id != 0 {
            match expr {
                Expression::Negated(poly) => {
                    Expression::Negated(Box::new(self.split_expression(name, *poly)))
                }
                Expression::Scaled(poly, v) => {
                    Expression::Scaled(Box::new(self.split_expression(name, *poly)), v)
                }
                Expression::Sum(a, b) => {
                    let a = self.split_expression(name, *a);
                    let b = self.split_expression(name, *b);
                    a + b
                }
                Expression::Product(a, b) => {
                    let (mut a, mut b) = (*a, *b);
                    while a.degree() + b.degree() > self.max_degree {
                        let mut split = |expr: Expression<F>| {
                            if expr.degree() > self.max_degree {
                                self.split_expression(name, expr)
                            } else {
                                let cell_type = C::storage_for_expr(&expr);
                                self.store_expression(name, expr, cell_type, None)
                            }
                        };
                        if a.degree() >= b.degree() {
                            a = split(a);
                        } else {
                            b = split(b);
                        }
                    }
                    a * b
                }
                _ => expr.clone(),
            }
        } else {
            expr.clone()
        }
    }

    pub(crate) fn print_stats(&self) {
        let mut expressions = self.constraints.clone();
        expressions.sort_by(|a, b| a.1.degree().cmp(&b.1.degree()));
        for (name, expr) in expressions.iter() {
            println!("'{}': {}", name, expr.degree());
        }
    }
}

/// General trait to convert to a vec
pub trait ToVec<T: Clone> {
    /// Converts a tuple to a vector
    fn to_vec(&self) -> Vec<T>;
}

impl<T: Clone> ToVec<T> for Vec<T> {
    fn to_vec(&self) -> Vec<T> {
        self.clone()
    }
}

impl<T: Clone> ToVec<T> for [T] {
    fn to_vec(&self) -> Vec<T> {
        self.to_owned()
    }
}

impl<T: Clone> ToVec<T> for &[T] {
    fn to_vec(&self) -> Vec<T> {
        <&[T]>::clone(self).to_owned()
    }
}

macro_rules! impl_to_vec {
    (($($t:ty),*), ($($v:ident),*)) => {
        impl<T: Clone> ToVec<T> for ($($t,)*) {
            fn to_vec(&self) -> Vec<T> {
                let ($($v,)*) = self;
                vec![$($v.clone()),*]
            }
        }
    };
}

impl_to_vec!((T, T), (a, b));
impl_to_vec!((T, T, T), (a, b, c));
impl_to_vec!((T, T, T, T), (a, b, c, d));
impl_to_vec!((T, T, T, T, T), (a, b, c, d, e));
impl_to_vec!((T, T, T, T, T, T), (a, b, c, d, e, f));
impl_to_vec!((T, T, T, T, T, T, T), (a, b, c, d, e, f, g));
impl_to_vec!((T, T, T, T, T, T, T, T), (a, b, c, d, e, f, g, h));
impl_to_vec!((T, T, T, T, T, T, T, T, T), (a, b, c, d, e, f, g, h, i));
impl_to_vec!(
    (T, T, T, T, T, T, T, T, T, T),
    (a, b, c, d, e, f, g, h, i, j)
);
impl_to_vec!(
    (T, T, T, T, T, T, T, T, T, T, T),
    (a, b, c, d, e, f, g, h, i, j, k)
);
impl_to_vec!(
    (T, T, T, T, T, T, T, T, T, T, T, T),
    (a, b, c, d, e, f, g, h, i, j, k, l)
);
impl_to_vec!(
    (T, T, T, T, T, T, T, T, T, T, T, T, T),
    (a, b, c, d, e, f, g, h, i, j, k, l, m)
);
impl_to_vec!(
    (T, T, T, T, T, T, T, T, T, T, T, T, T, T),
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n)
);

/// Trait that generates a vector of expressions
pub trait ExprVec<F> {
    /// Returns a vector of the expressions from itself
    fn to_expr_vec(&self) -> Vec<Expression<F>>;
}

impl<F: Field> ExprVec<F> for std::ops::Range<usize> {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.clone().map(|e| e.expr()).collect::<Vec<_>>()
    }
}

impl<F: Field, E: Expr<F>> ExprVec<F> for Vec<E> {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.iter().map(|e| e.expr()).collect::<Vec<_>>()
    }
}

impl<F: Field, E: Expr<F>> ExprVec<F> for [E] {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.iter().map(|e| e.expr()).collect::<Vec<_>>()
    }
}

impl<F: Field, E: Expr<F>> ExprVec<F> for &[E] {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.iter().map(|e| e.expr()).collect::<Vec<_>>()
    }
}


/// Implementation trait `ExprVec` for type able to be casted to an
/// Expression
#[macro_export]
macro_rules! impl_expr_vec {
    ($type:ty) => {
        impl<F: eth_types::Field> ExprVec<F> for $type {
            #[inline]
            fn to_expr_vec(&self) -> Vec<Expression<F>> {
                vec![self.expr()]
            }
        }
    };
}

impl_expr_vec!(bool);
impl_expr_vec!(u8);
impl_expr_vec!(i32);
impl_expr_vec!(u64);
impl_expr_vec!(usize);
impl_expr_vec!(Expression<F>);
impl_expr_vec!(Cell<F>);

/// Newtype wrapper for `Vec<Expression<F>>`
#[derive(Clone)]
pub struct ExpressionVec<F: Field>(pub Vec<Expression<F>>);

impl<F: Field> Add for ExpressionVec<F> {
    type Output = ExpressionVec<F>;

    fn add(self, rhs: ExpressionVec<F>) -> Self::Output {
        ExpressionVec(
            self.0
                .iter()
                .zip(rhs.0.iter())
                .map(|(a, b)| a.expr() + b.expr())
                .collect(),
        )
    }
}

impl<F: Field> Mul for ExpressionVec<F> {
    type Output = ExpressionVec<F>;

    fn mul(self, rhs: ExpressionVec<F>) -> Self::Output {
        ExpressionVec(
            self.0
                .iter()
                .zip(rhs.0.iter())
                .map(|(a, b)| a.expr() * b.expr())
                .collect(),
        )
    }
}

/// Trait for doing math on Expressions, no matter the type they are stored in
pub trait ExprResult<F> {
    /// Adds two values together
    fn add(&self, other: &Self) -> Self;
    /// Multiply with a scalar
    fn mul(&self, other: &Expression<F>) -> Self;
}

impl<F: Field> ExprResult<F> for () {
    fn add(&self, _other: &Self) -> Self {}
    fn mul(&self, _other: &Expression<F>) -> Self {}
}

impl<F: Field> ExprResult<F> for Vec<Expression<F>> {
    fn add(&self, other: &Self) -> Self {
        (ExpressionVec(self.clone()) + ExpressionVec(other.clone())).0
    }
    fn mul(&self, other: &Expression<F>) -> Self {
        (ExpressionVec(self.clone()) * ExpressionVec(vec![other.clone(); self.len()])).0
    }
}

impl<F: Field> ExprResult<F> for Expression<F> {
    fn add(&self, other: &Self) -> Self {
        vec![self.clone()].add(&vec![other.clone()])[0].clone()
    }
    fn mul(&self, other: &Expression<F>) -> Self {
        vec![self.clone()].mul(other)[0].clone()
    }
}

/// Implement `ExprResult` for tupples
#[macro_export]
macro_rules! impl_expr_result {
    ($($type:ty),*) => {
        impl<F: eth_types::Field> ExprResult<F> for ($($type),*) {
            fn add(&self, other: &Self) -> Self {
                self.to_vec().add(&other.to_vec()).into_iter().collect_tuple().unwrap()
            }
            fn mul(&self, other: &Expression<F>) -> Self {
                self.to_vec().mul(other).into_iter().collect_tuple().unwrap()
            }
        }
    };
}

impl_expr_result!(Expression<F>, Expression<F>);
impl_expr_result!(Expression<F>, Expression<F>, Expression<F>);
impl_expr_result!(Expression<F>, Expression<F>, Expression<F>, Expression<F>);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);

/// Trait around RLC
pub trait RLCable<F: Field> {
    /// Returns the RLC of itself
    fn rlc(&self, r: &Expression<F>) -> Expression<F>;
    /// Returns the RLC of the reverse of itself
    fn rlc_rev(&self, r: &Expression<F>) -> Expression<F>;
}

impl<F: Field, E: ExprVec<F> + ?Sized> RLCable<F> for E {
    fn rlc(&self, r: &Expression<F>) -> Expression<F> {
        rlc::expr(&self.to_expr_vec(), r.expr())
    }

    fn rlc_rev(&self, r: &Expression<F>) -> Expression<F> {
        rlc::expr(
            &self.to_expr_vec().iter().rev().cloned().collect_vec(),
            r.expr(),
        )
    }
}

/// Trait around RLC
pub trait RLCChainable<F> {
    /// Returns the RLC of itself with a starting rlc/multiplier
    fn rlc_chain(&self, other: Expression<F>) -> Expression<F>;
}

impl<F: Field> RLCChainable<F> for (Expression<F>, Expression<F>) {
    fn rlc_chain(&self, other: Expression<F>) -> Expression<F> {
        self.0.expr() + self.1.expr() * other.expr()
    }
}

/// Trait around RLC
pub trait RLCChainableRev<F> {
    /// Returns the RLC of itself with a starting rlc/multiplier
    fn rlc_chain_rev(&self, other: (Expression<F>, Expression<F>)) -> Expression<F>;
}

impl<F: Field> RLCChainableRev<F> for Expression<F> {
    fn rlc_chain_rev(&self, other: (Expression<F>, Expression<F>)) -> Expression<F> {
        self.expr() * other.1.expr() + other.0.expr()
    }
}

/// Trait around RLC
pub trait RLCableValue<F> {
    /// Returns the RLC of itself
    fn rlc_value(&self, r: F) -> F;
    /// Returns the RLC of the reverse of itself
    fn rlc_value_rev(&self, r: F) -> F;
}

impl<F: Field> RLCableValue<F> for Vec<u8> {
    fn rlc_value(&self, r: F) -> F {
        rlc::value(self, r)
    }
    fn rlc_value_rev(&self, r: F) -> F {
        rlc::value(&self.iter().rev().cloned().collect_vec(), r)
    }
}

impl<F: Field> RLCableValue<F> for [u8] {
    fn rlc_value(&self, r: F) -> F {
        rlc::value(self, r)
    }
    fn rlc_value_rev(&self, r: F) -> F {
        rlc::value(&self.iter().rev().cloned().collect_vec(), r)
    }
}

/// Trait around RLC
pub trait RLCChainableValue<F, S, I> {
    /// Returns the RLC of itself with a starting rlc/multiplier
    fn rlc_chain_value(&self, values: I, r: F) -> (F, F);
}

impl<F: Field, S: Scalar<F>, I: IntoIterator<Item = S>> RLCChainableValue<F, S, I> for (F, F) {
    fn rlc_chain_value(&self, values: I, r: F) -> (F, F) {
        let mut rlc = self.0;
        let mut mult = self.1;
        for value in values.into_iter().map(|byte| byte.scalar()) {
            rlc += value * mult;
            mult *= r;
        }
        (rlc, mult)
    }
}
/// require_parser
#[macro_export]
macro_rules! require_parser {
    {
        $cb:expr,
        lhs = ($($lhs:tt)*)
        rest = (== $($rhs:tt)*)
    } => {
        let description = $crate::concat_with_preamble!(
            stringify!($($lhs)*),
            " == ",
            stringify!($($rhs)*)
        );
        $crate::_require!($cb, description, $($lhs)* => $($rhs)*)
    };

    {
        $cb:expr,
        lhs = ($($lhs:tt)*)
        rest = ($next:tt $($rest:tt)*)
    } => {
        $crate::require_parser! {
            $cb,
            lhs = ($($lhs)* $next)
            rest = ($($rest)*)
        }
    };
}

/// _require2
#[macro_export]
macro_rules! _require2 {
    ($cb:expr, $($rest:tt)*) => {{
        $crate::require_parser! {
            $cb,
            lhs = ()
            rest = ($($rest)*)
        }
    }};
}

/// Creates a dummy constraint builder that cannot be used to add constraints.
#[macro_export]
macro_rules! _cb {
    () => {{
        use $crate::circuit_tools::cell_manager::DefaultCellType;
        ConstraintBuilder::<F, DefaultCellType>::new(0, None, None)
    }};
}

/// Concats arguments with preamble consisting of the originating file and line.
#[macro_export]
macro_rules! concat_with_preamble {
    ($($args:expr),* $(,)?) => {{
        concat!(
            file!(),
            ":",
            line!(),
            ": ",
            $(
                $args,
            )*
        )
    }};
}

/// Can be used to mark a specific branch as unreachable
#[macro_export]
macro_rules! _unreachablex {
    ($cb:expr $(,$descr:expr)?) => {{
        let descr = concat_with_preamble!(
            "unreachable executed",
            $(
                ": ",
                $descr,
            )*
        );
        _require!($cb, descr, true => false)
    }};
}

/// _require
#[macro_export]
macro_rules! _require {
    ($cb:expr, $lhs:expr => bool) => {{
        let description = concat_with_preamble!(
            stringify!($lhs),
            " => ",
            "bool",
        );
        $cb.require_boolean(description, $lhs.expr());
    }};

    ($cb:expr, $lhs:expr => $rhs:expr) => {{
        let description = concat_with_preamble!(
            stringify!($lhs),
            " => ",
            stringify!($rhs)
        );
        _require!($cb, description, $lhs => $rhs)
    }};

    ($cb:expr, $descr:expr, $lhs:expr => $rhs:expr) => {{
        let lhs = $lhs.to_expr_vec();
        let rhs = $rhs.to_expr_vec();
        if lhs.len() == rhs.len() {
            for (lhs, rhs) in lhs.iter().zip(rhs.iter()) {
                $cb.require_equal(
                    Box::leak($descr.to_string().into_boxed_str()),
                    lhs.expr(),
                    rhs.expr(),
                );
            }
        } else if lhs.len() == 1 && rhs.len() > 1 {
            $cb.require_in_set(
                Box::leak($descr.to_string().into_boxed_str()),
                lhs[0].expr(),
                rhs.clone(),
            );
        } else {
            unreachable!()
        }
    }};

    // Store tuple
    ($cb:expr, $values:expr =>> @$tag:expr) => {{
        let description = concat_with_preamble!(
            stringify!($values),
            " =>> @",
            stringify!($tag),
        );
        $cb.store_tuple(
            description,
            $tag,
            $values,
        );
    }};
    ($cb:expr, $descr:expr, $values:expr =>> @$tag:expr) => {{
        $cb.store_tuple(
            Box::leak($descr.to_string().into_boxed_str()),
            $tag,
            $values,
        );
    }};

    // Do lookup
    ($cb:expr, $values:expr => @$table:expr) => {{
        let description = concat_with_preamble!(
            stringify!($values),
            " => @",
            stringify!($tag),
        );
        $cb.add_lookup(
            description.to_string(),
            $values,
            $table,
        );
    }};
    ($cb:expr, $descr:expr, $values:expr => @$table:expr) => {{
        $cb.add_lookup(
            Box::leak($descr.into_boxed_str()),
            $values,
            $table,
        );
    }};

    // Put values in a lookup table using a tuple
    ($cb:expr, @$table:expr => $values:expr) => {{
        let description = concat_with_preamble!(
            "@",
            stringify!($table),
            " => (",
            stringify!($values),
            ")",
        );
        $cb.store_table(
            description,
            $table,
            $values,
        );
    }};
}

/// matchx
/// Supports `_` which works the same as in the normal `match`: if none of the
/// other arms are active the `_` arm will be executed and so can be used to
/// return some default values or could also be marked as unreachable (using the
/// unreachablex! macro).
#[macro_export]
macro_rules! _matchx {
    ($cb:expr, ($($condition:expr => $when:expr),* $(, _ => $catch_all:expr)? $(,)?))  => {{
        let mut conditions = Vec::new();
        let mut cases = Vec::new();
        $(
            $cb.push_condition($condition.expr());
            let ret = $when.clone();
            $cb.pop_condition();
            cases.push(($condition.expr(), ret));
            conditions.push($condition.expr());
        )*

        $(
            let catch_all_condition = not::expr(sum::expr(&conditions));
            $cb.push_condition(catch_all_condition.expr());
            let ret = $catch_all;
            $cb.pop_condition();
            cases.push((catch_all_condition.expr(), ret));
            conditions.push(catch_all_condition.expr());
        )*

        // All conditions need to be boolean
        for condition in conditions.iter() {
            _require!($cb, condition => bool);
        }
        // Exactly 1 case needs to be enabled
        _require!($cb, sum::expr(&conditions) => 1);

        // Apply the conditions to all corresponding values
        let mut res = cases[0].1.mul(&cases[0].0.expr());
        for pair in cases.iter().skip(1) {
            res = <_ as ExprResult<F>>::add(&res, &pair.1.mul(&pair.0.expr()));
        }
        res
    }};
}

#[macro_export]
macro_rules! _to_and {
    (($($condition:expr),*)) => {
        and::expr([$($condition.expr()),*])
    };
    ($condition:expr) => {
        $condition.expr()
    }
}
/// ifx
#[macro_export]
macro_rules! _ifx {
    ($cb:expr,$condition:tt => $when_true:block $(elsex $when_false:block)?)  => {{
        let condition = _to_and!($condition);

        $cb.push_condition(condition.expr());
        let ret_true = $when_true;
        $cb.pop_condition();

        #[allow(unused_assignments, unused_mut)]
        let mut ret = ret_true.mul(&condition.expr());
        $(
            // In if/else cases, the condition needs to be boolean
            _require!($cb, condition => bool);

            $cb.push_condition(not::expr(condition.expr()));
            let ret_false = $when_false;
            $cb.pop_condition();

            ret = <_ as ExprResult<F>>::add(&ret_true.mul(&condition), &ret_false.mul(&not::expr(condition.expr())));
        )*
        ret
    }};
}

/// matchw - Resembles matchx so that the witness generation can look like the
/// circuit code.
#[macro_export]
macro_rules! matchw {
    ($($condition:expr => $when:expr),* $(, _ => $catch_all:expr)? $(,)?)  => {{
        if false {
            unreachable!()
        }
        $(else if $condition {
            $when
        }
        )*
        else {
            $(
                $catch_all
            )*
            unreachable!()
        }
    }};
}

/// assign advice
#[macro_export]
macro_rules! assign {
    // Column
    ($region:expr, ($column:expr, $offset:expr) => $value:expr) => {{
        use halo2_proofs::circuit::Value;
        let description =
            $crate::concat_with_preamble!(stringify!($column), " => ", stringify!($value));
        let value: F = $value;
        $region.assign_advice(|| description, $column, $offset, || Value::known(value))
    }};
    ($region:expr, ($column:expr, $offset:expr) => $annotation:expr, $value:expr) => {{
        use halo2_proofs::circuit::Value;
        let value: F = $value;
        $region.name_column(|| $annotation, $column);
        $region.assign_advice(|| "", $column, $offset, || Value::known(value))
    }};
    // Cell
    ($region:expr, $cell:expr, $offset:expr => $value:expr) => {{
        use halo2_proofs::circuit::Value;
        let description =
            $crate::concat_with_preamble!(stringify!($cell), " => ", stringify!($value));
        let value: F = $value;
        $region.assign_advice(
            || description,
            $cell.column(),
            $offset + $cell.rotation(),
            || Value::known(value),
        )
    }};
    ($region:expr, $cell:expr, $offset:expr => $annotation:expr, $value:expr) => {{
        use halo2_proofs::circuit::Value;
        let value: F = $value;
        $region.assign_advice(
            || $annotation,
            $cell.column(),
            $offset + $cell.rotation(),
            || Value::known(value),
        )
    }};
}

/// assign fixed
#[macro_export]
macro_rules! assignf {
    ($region:expr, ($column:expr, $offset:expr) => $value:expr) => {{
        let description =
            $crate::concat_with_preamble!(stringify!($column), " => ", stringify!($value));
        let value: F = $value;
        $region.assign_fixed(|| description, $column, $offset, || Value::known(value))
    }};
}

#[macro_export]
macro_rules! _to_values_vec {
    (($($tts:expr), *)) => {
        vec![$($tts.expr()), *]
    };
}

#[macro_export]
macro_rules! _to_options_vec {
    (($($tts:expr), *)) => {
        vec![$($tts), *]
    };
}
/// Circuit builder macros
/// Nested macro's can't do repetition <https://github.com/rust-lang/rust/issues/35853>
/// so we expose a couple of permutations here manually.
#[macro_export]
macro_rules! circuit {
    ([$meta:expr, $cb:expr], $content:block) => {{
        #[allow(unused_imports)]
        use zkevm_gadgets::util::{and, not, or, sum, Expr};
        #[allow(unused_imports)]
        use $crate::constraint_builder::{ExprResult, ExprVec};
        #[allow(unused_imports)]
        use $crate::{
            _ifx, _matchx, _require, _to_and, _to_options_vec, _to_values_vec, _unreachablex,
            concat_with_preamble,
        };

        #[allow(unused_macros)]
        macro_rules! f {
            ($column:expr, $rot:expr) => {{
                $meta.query_fixed($column.clone(), Rotation($rot as i32))
            }};
            ($column:expr) => {{
                $meta.query_fixed($column.clone(), Rotation::cur())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! a {
            ($column:expr, $rot:expr) => {{
                $meta.query_advice($column.clone(), Rotation($rot as i32))
            }};
            ($column:expr) => {{
                $meta.query_advice($column.clone(), Rotation::cur())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! c {
            ($column:expr) => {{
                $meta.query_challenge($column.clone())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! q {
            ($column:expr) => {{
                $meta.query_selector($column.clone())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! x {
            ($column:expr, $rot:expr) => {{
                $meta.query_any($column.clone(), Rotation($rot as i32))
            }};
            ($column:expr) => {{
                $meta.query_any($column.clone(), Rotation::cur())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! not {
            ($expr:expr) => {{
                crate::util::not::expr($expr.expr())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! invert {
            ($expr:expr) => {{
                Expression::Constant(F::from($expr as u64).invert().unwrap())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! require {
            ($lhs:expr => bool) => {{
                _require!($cb, $lhs => bool);
            }};
            ($lhs:expr => $rhs:expr) => {{
                _require!($cb, $lhs => $rhs);
            }};
            ($name:expr, $lhs:expr => $rhs:expr) => {{
                _require!($cb, $name, $lhs => $rhs);
            }};
            // Store tuple
            ($values:tt =>> @$tag:expr) => {{
                let values = _to_values_vec!($values);
                _require!($cb, values =>> @$tag);
            }};
            ($descr:expr, $values:tt =>> @$tag:expr) => {{
                let values = _to_values_vec!($values);
                _require!($cb, $descr, values =>> @$tag);
            }};
            // Do lookups
            ($values:tt => @$table:expr) => {{
                let values = _to_values_vec!($values);
                _require!($cb, values => @$table);
            }};
            ($descr:expr, $values:tt => @$table:expr) => {{
                let values = _to_values_vec!($values);
                _require!($cb, $descr, values => @$table);
            }};
            // Build lookup tables
            (@$table:expr => $values:expr) => {{
                _require!($cb, @$table => $values);
            }};
        }

        #[allow(unused_macros)]
        macro_rules! ifx {
                                ($condition:tt => $when_true:block elsex $when_false:block) => {{
                                    _ifx!($cb, ($condition) => $when_true elsex $when_false)
                                }};
                                ($condition:expr => $when_true:block elsex $when_false:block) => {{
                                    _ifx!($cb, $condition => $when_true elsex $when_false)
                                }};

                                ($condition:tt => $when_true:block) => {{
                                    _ifx!($cb, $condition => $when_true)
                                }};
                                ($condition:expr => $when_true:block) => {{
                                    _ifx!($cb, $condition => $when_true)
                                }};
                            }

        #[allow(unused_macros)]
        macro_rules! matchx {
            ($condition_to_when:tt) => {{
                _matchx!($cb, $condition_to_when)
            }};
        }

        #[allow(unused_macros)]
        macro_rules! unreachablex {
            () => {{
                _unreachablex!($cb)
            }};
            ($arg:expr) => {{
                _unreachablex!($cb, $arg)
            }};
        }

        $content
    }};
}
