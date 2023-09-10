use eth_types::Field;
use zkevm_circuits::{evm_circuit::table::FixedTableTag, util::query_expression};
use zkevm_gadgets::impl_expr;
use crate::{util::Scalar, cell_manager::{CellManager, Cell}};
use halo2_proofs::{
    plonk::{Circuit, ConstraintSystem, Expression, Advice, Fixed, Column, FirstPhase, Challenge, Error, SecondPhase}, 
    circuit::{SimpleFloorPlanner, Layouter, layouter, Value},
    poly::Rotation,
};

use crate::{constraint_builder:: ConstraintBuilder, cell_manager::CellType};

#[derive(Clone)]
pub struct TestConfig<F>{
    q_enable: Column<Fixed>,
    fixed_table: [Column<Fixed>; 2],
    cells: (Cell<F>, Cell<F>, Cell<F>, Cell<F>, Cell<F>),
    rand: Challenge,
    cb: ConstraintBuilder<F, TestCellType>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TableTag {
    Fixed,
    Dyn
}
impl_expr!(TableTag);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TestCellType {
    StoragePhase1,
    StoragePhase2,
}
impl CellType for TestCellType{
    type TableType = TableTag;

    fn lookup_table_type(&self) -> Option<Self::TableType> {Some(TableTag::Fixed)}
    fn byte_type() -> Option<Self> {None}
    fn create_type(id: usize) -> Self {unreachable!()}
    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            1 => Self::StoragePhase1,
            2 => Self::StoragePhase2,
            _ => unreachable!()
        }
    }
}
impl Default for TestCellType {
    fn default() -> Self {Self::StoragePhase1}
}


impl<F: Field> TestConfig<F> {
    pub fn new(meta: &mut ConstraintSystem<F>, r0: Challenge) -> Self {
        let q_enable = meta.fixed_column();
        let r1 = meta.challenge_usable_after(FirstPhase);
        let fixed_table: [Column<Fixed>; 2] = (0..2)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let r0 = query_expression(meta, |meta| meta.query_challenge(r0));
        let mut cb: ConstraintBuilder<F, TestCellType> =  ConstraintBuilder::new(4,  None, Some(r0));
        cb.load_table(meta, TableTag::Fixed, &fixed_table);

        let mut cm = CellManager::new(5, 0);
        cm.add_columns(meta, &mut cb, TestCellType::StoragePhase1, 1, false, 1);
        cm.add_columns(meta, &mut cb, TestCellType::StoragePhase2, 2, false, 1);
        cb.set_cell_manager(cm);
        
        let a = cb.query_default();
        let b = cb.query_default();
        let c = cb.query_default();
        let d = cb.query_default();
        let e = cb.query_cell_with_type(TestCellType::StoragePhase2);
        
        meta.create_gate("Test", |meta| {
            circuit!([meta, cb], {
                ifx!(f!(q_enable) => {
                    // Lookup the sum of a,b and the sum of c,d in the fixed_table
                    require!((a.expr() + b.expr(), c.expr() + d.expr()) => @cb.table(TableTag::Fixed));

                    // Store random linear combination of c,d in a phase2 cell
                    let rlc = c.expr() + d.expr() * c!(r1);
                    // Correct store during assignment is garenteed by this equality constriant
                    require!(e.expr() => rlc.clone());

                    // Perform dynamic lookup on cell e and its corresponding value
                    // we do this just for demo: if e == rlc then {c} is a subset of {rlc}
                    require!((TableTag::Dyn.expr(), e.expr()) => @vec![TableTag::Dyn.expr(), rlc]);
                   
                });
            });
            cb.build_constraints()
        });
        TestConfig { 
            q_enable,
            rand: r1,
            cells: (a, b, c, d, e),
            fixed_table,
            cb,
        }
    }

    pub fn assign(
        &self, 
        layouter: &mut impl Layouter<F>,
        rand: F,
    ) -> Result<(), Error> {
        let mut rand = F::ZERO;
        layouter.get_challenge(self.rand).map(|r| rand = r);
        layouter.assign_region(
            || "Test", 
            |mut region| {
                assignf!(region, (self.q_enable, 0) => true.scalar());
                let (a, b, c, d,  e) = &self.cells;
                assign!(region, a, 0 => 1.scalar())?;
                assign!(region, b, 0 => 2.scalar())?;
                assign!(region, c, 0 => 3.scalar())?;
                assign!(region, d, 0 => 4.scalar())?;
                let rlc = F::from(3) + F::from(4) * rand;
                assign!(region, e, 0 => rlc)?;
                Ok(())
            }
        )
    }
}

#[derive(Clone, Debug, Default)]
struct TestCircuit<F> {
    _phantom: F,
}

impl<F: Field> Circuit<F> for TestCircuit<F> {
    type Config = TestConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // dummy column for phase1 challange
        meta.advice_column_in(FirstPhase);
        let randomness = meta.challenge_usable_after(FirstPhase); 
        let config = TestConfig::new(meta, randomness);
        config
    }

    fn synthesize(
        &self, 
        config: Self::Config, 
        mut layouter: impl Layouter<F>
    ) -> Result<(), halo2_proofs::plonk::Error> {
        layouter.assign_region(|| "fixed table", |mut region| {
            assignf!(region, (config.fixed_table[0], 0) => (1 + 2).scalar())?;
            assignf!(region, (config.fixed_table[1], 0) => (3 + 4).scalar())?;
            Ok(())
        });
        Ok(())
    }
}

#[test]
fn test() {

    use halo2_proofs::{ dev::MockProver, halo2curves::bn256::Fr};

    let circuit = TestCircuit::<Fr>::default();
    let prover = MockProver::<Fr>::run(6, &circuit, vec![]).unwrap();
    prover.assert_satisfied_par();
}