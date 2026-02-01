use std::{
    fmt::{self, Display, Formatter},
    path::Path,
};

#[derive(Debug, Copy, Clone)]
pub(crate) struct Location<'a> {
    f: &'a Path,
    s: (usize, usize),
    e: (usize, usize),
}

impl<'a> Display for Location<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.s.0 == self.e.0 {
            write!(
                f,
                "{}:{}.{}-{}",
                self.f.display(),
                self.s.0,
                self.s.1,
                self.e.1
            )
        } else {
            write!(
                f,
                "{}:{}.{}-{}.{}",
                self.f.display(),
                self.s.0,
                self.s.1,
                self.e.0,
                self.e.1
            )
        }
    }
}

pub(crate) type Located<'a, T> = (Location<'a>, T);

pub(crate) trait Wrapper<'a, W, T> {
    fn map<F, U>(self, f: F) -> (W, U)
    where
        F: Fn(T) -> U;

    fn raw(self) -> T;

    fn wrapper(&self) -> W;
}

impl<'a, T> Wrapper<'a, Location<'a>, T> for Located<'a, T> {
    fn map<F, U>(self, f: F) -> Located<'a, U>
    where
        F: Fn(T) -> U,
    {
        (self.0, f(self.1))
    }

    fn raw(self) -> T {
        self.1
    }

    fn wrapper(&self) -> Location<'a> {
        self.0
    }
}
