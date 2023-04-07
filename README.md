Many structures which model real-world relations involve aliasing, which can be modeled in Rust with types like [`Rc<T>`].
However, [`Rc<T>`] is immutable, which is often problematic when initializing aliasing structures.
Because of this, it is often the case that interior mutability is used, such as [`Rc<RefCell<T>>`].

Unfortunately, there is no safe way to convert from [`Rc<RefCell<T>>`] to [`Rc<T>`],
which means these aliasing structures are often permanently left in their mutable form.
Aside from causing the uncertainty of later mutation,
this also introduces inefficiency because all accesses (even immutable ones) are
passed through the runtime-level borrowing logic of [`RefCell<T>`].
To combat this issue, `mut-rc` introduces a new type called [`MutRc<T>`].

[`MutRc<T>`] is essentially equivalent to [`Rc<RefCell<T>>`],
but can be "finalized" into a plain [`Rc<T>`] at the end of its mutable lifetime,
all while preserving the created aliasing topology.

## Example

```rust
# use std::rc::Rc;
# use mut_rc::MutRc;
let a: MutRc<i32> = 45.into(); // create a MutRc<i32> value and an alias
let b = a.clone();

a.with_mut(|x| *x *= 2).unwrap(); // mutate the value via callback

let fa: Rc<i32> = a.finalize().unwrap(); // finalize the values into Rc<i32>
let fb: Rc<i32> = b.finalize().unwrap();

assert_eq!(*fb, 90);
assert!(Rc::ptr_eq(&fa, &fb)); // aliasing topology is preserved
```

## no-std

This crate supports building in `no-std` environments by disabling default features:

```toml
[dependencies]
mut-rc = { version = "...", use-default-features = false }
```

Note that the `alloc` crate is still required in this case.
