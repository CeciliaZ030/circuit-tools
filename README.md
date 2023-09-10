# circuit-tools
A lightweit SDK for Halo2 frontend circuit.
## Features
### Logic: Constraint Builder
Leverage Rust's macro to construct conditional constraints based on execution branching. Build all constraints in on step with Halo2's gate.
```
let mut cb: ConstraintBuilder<F, TestCellType> =  ConstraintBuilder::new(4,  None, None);

meta.create_gate("Test", |meta| {
    circuit!([meta, cb], {
        ifx!(f!(q_enable) => {
            ifx!{a!(a) => {
                require!(a!(res) => a!(b) + f!(c)); 
            } elsex {
                require!(a!(res) => a!(b) + c!(r));  
            }};
        });
    });
    cb.build_constraints()
});
```
### Data: Cell Manager
Manage and allocate cells on demand based on user specified `CellType`. Decrease amount of columns space wasted, enable degree reduction and lookup automation.
```
let mut cm = CellManager::new(5, 0);
cm.add_columns(meta, &mut cb, TestCellType::StoragePhase1, 1, false, 1);
cm.add_columns(meta, &mut cb, TestCellType::Lookup, 2, false, 1);

// Allocation
let a = cb.query_default();
let b = cb.query_default();
let c = cb.query_cell_with_type(TestCellType::StoragePhase2);

// Computation
require!(c.expr() => a.expr() + b.expr() * challenge.expr());
// Lookup
require!((a.expr(), b.expr()) =>> @TestCellType::Lookup);

```
### Memory: Dynamic Lookup
Abstraction over using dynamic lookup to prove RW access in RAM. Stores to dynamic table to resemble WRITE and add lookups to represent READ. Lookup operation `(idx, r0, r1) => (rdx, w0, w1)` returns true if and only if the prover access the writen data at anticipated position correctly.
```
let mut memory = Memory::new();
memory.add_rw(meta, &mut cb.base, &mut state_cm, MyCellType::Mem1, 1);
memory.add_rw(meta, &mut cb.base, &mut state_cm, MyCellType::Mem2, 1);

let register1 = memory[MyCellType::Mem1];
let register2 = memory[MyCellType::Mem2];

register1.store(cb, &[a0, b0]);
register2.store(cb, &[c0, d9, 123.expr()]);

// ... long time later ...
register2.load(cb, &[c1, d1, 123.expr()]);
register1.load(cb, &[a0, b1]);

```
