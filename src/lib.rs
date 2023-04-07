#![no_std]
#![forbid(unsafe_code)]

#![doc = include_str!("../README.md")]

#[cfg_attr(test, macro_use)]
extern crate alloc;

use core::cell::{RefCell, BorrowError, BorrowMutError};
use alloc::rc::Rc;

/// An error resulting from [`MutRc::with_mut`].
#[derive(Debug)]
pub enum MutateError {
    /// The shared value is already borrowed.
    /// This can be caused if the same shared value is accessed from within [`MutRc::with`] or [`MutRc::with_mut`].
    BorrowMutError(BorrowMutError),
    /// There exists an aliasing [`Rc<T>`] returned by [`MutRc::finalize`] on the same shared value.
    Finalized,
}

/// A temporarily-mutable version of [`Rc`].
/// 
/// [`MutRc<T>`] is essentially equivalent to [`Rc<RefCell<T>>`] except that it can be "finalized" into an [`Rc<T>`] once mutation is no longer needed.
/// This operation preserves the original aliasing topology, and is useful for initializing aliasing structures
/// that initially need mutability, but later can be converted to an immutable form.
/// 
/// All operations on [`MutRc`] are guaranteed to not panic.
#[derive(Debug, Default)]
pub struct MutRc<T>(Rc<RefCell<Rc<T>>>);
impl<T> MutRc<T> {
    /// Creates a new, unaliased instance of [`MutRc<T>`] with the given initial value.
    pub fn new(value: T) -> Self {
        Self(Rc::new(RefCell::new(Rc::new(value))))
    }
    /// Accesses the shared value immutably, optionally returning the result of the callback.
    /// 
    /// This operation can fail if the shared value is already borrowed mutably (i.e., if called from within [`MutRc::with_mut`] on the same shared value).
    pub fn with<U, F: FnOnce(&T) -> U>(&self, f: F) -> Result<U, BorrowError> {
        Ok(f(&*self.0.try_borrow()?))
    }
    /// Accesses the shared value mutably, optionally returning the result of the callback.
    /// 
    /// This operation can fail if the shared value is already borrowed (i.e., if called from within [`MutRc::with`] or [`MutRc::with_mut`] on the same shared value),
    /// or if there exists an aliasing [`Rc<T>`] returned by [`MutRc::finalize`] on the same shared value.
    /// 
    /// If recursion is needed, but mutation is not, consider using [`MutRc::with`] instead.
    pub fn with_mut<U, F: FnOnce(&mut T) -> U>(&self, f: F) -> Result<U, MutateError> {
        match self.0.try_borrow_mut() {
            Ok(mut x) => match Rc::get_mut(&mut *x) {
                Some(x) => Ok(f(x)),
                None => Err(MutateError::Finalized),
            }
            Err(e) => Err(MutateError::BorrowMutError(e)),
        }
    }
    /// Finalizes the value into an (immutable) aliasing instance of [`Rc<T>`].
    /// While this aliasing [`Rc<T>`] exists, all subsequent calls to [`MutRc::with_mut`] on the same shared value will fail.
    /// 
    /// This operation can fail if the shared value is already borrowed mutably (i.e., if called from within [`MutRc::with_mut`] on the same shared value).
    pub fn finalize(&self) -> Result<Rc<T>, BorrowError> {
        Ok(self.0.try_borrow()?.clone())
    }

    // -------------------------------------------------------------

    /// Checks if two instances of [`MutRc<T>`] are aliases to the same value.
    pub fn ptr_eq(this: &MutRc<T>, other: &MutRc<T>) -> bool {
        Rc::ptr_eq(&this.0, &other.0)
    }
}
impl<T> Clone for MutRc<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<T> From<T> for MutRc<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

#[test]
fn test_basic() {
    #[derive(Debug)]
    struct NoClone(i32);

    let a = MutRc::new(NoClone(45));
    let b = a.clone();
    let c = MutRc::new(NoClone(45));

    assert!(MutRc::ptr_eq(&a, &b));
    assert!(!MutRc::ptr_eq(&a, &c));
    assert!(!MutRc::ptr_eq(&b, &c));

    assert_eq!(a.with(|x| x.0).unwrap(), 45);
    assert_eq!(b.with(|x| x.0).unwrap(), 45);
    assert_eq!(c.with(|x| x.0).unwrap(), 45);

    a.with_mut(|x| x.0 = -23).unwrap();

    match a.with_mut(|_| a.with_mut(|_| ())) {
        Ok(Err(MutateError::BorrowMutError(_))) => (),
        x => panic!("{x:?}"),
    }

    assert_eq!(a.with(|x| x.0).unwrap(), -23);
    assert_eq!(b.with(|x| x.0).unwrap(), -23);
    assert_eq!(c.with(|x| x.0).unwrap(), 45);

    assert_eq!(a.with(|_| a.with(|x| x.0).unwrap()).unwrap(), -23);
    assert_eq!(b.with(|_| b.with(|x| x.0).unwrap()).unwrap(), -23);
    assert_eq!(c.with(|_| c.with(|x| x.0).unwrap()).unwrap(), 45);

    a.finalize().unwrap();
    b.finalize().unwrap();
    c.finalize().unwrap();

    b.with_mut(|x| x.0 = 17).unwrap();
    c.with_mut(|x| x.0 = 12).unwrap();

    assert_eq!(a.with(|_| a.with(|x| x.0).unwrap()).unwrap(), 17);
    assert_eq!(b.with(|_| b.with(|x| x.0).unwrap()).unwrap(), 17);
    assert_eq!(c.with(|_| c.with(|x| x.0).unwrap()).unwrap(), 12);

    let fa = a.finalize().unwrap();
    let fb = b.finalize().unwrap();
    let fc = c.finalize().unwrap();

    match (a.with_mut(|_| ()), b.with_mut(|_| ()), c.with_mut(|_| ())) {
        (Err(MutateError::Finalized), Err(MutateError::Finalized), Err(MutateError::Finalized)) => (),
        x => panic!("{x:?}"),
    }

    assert!(Rc::ptr_eq(&fa, &fb));
    assert!(!Rc::ptr_eq(&fa, &fc));
    assert!(!Rc::ptr_eq(&fb, &fc));

    assert_eq!(fa.0, 17);
    assert_eq!(fb.0, 17);
    assert_eq!(fc.0, 12);

    assert_eq!(a.with(|x| x.0).unwrap(), 17);
    assert_eq!(b.with(|x| x.0).unwrap(), 17);
    assert_eq!(c.with(|x| x.0).unwrap(), 12);

    assert_eq!(a.with(|_| a.with(|x| x.0).unwrap()).unwrap(), 17);
    assert_eq!(b.with(|_| b.with(|x| x.0).unwrap()).unwrap(), 17);
    assert_eq!(c.with(|_| c.with(|x| x.0).unwrap()).unwrap(), 12);
}
#[test]
fn test_traits() {
    let a: MutRc<i32> = Default::default();
    assert_eq!(a.with(|x| *x).unwrap(), 0);
    let fa = a.finalize().unwrap();
    assert_eq!(*fa, 0);

    let s = format!("{a:?}");
    assert!(!s.is_empty());

    let b: MutRc<u64> = 475.into();
    assert_eq!(b.with(|x| *x).unwrap(), 475);
    let fb = b.finalize().unwrap();
    assert_eq!(*fb, 475);
}
