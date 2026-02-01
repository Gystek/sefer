use std::{fmt::{self, Display, Formatter}, path::Path};

#[derive(Debug, Copy, Clone)]
pub(crate) struct Location<'a> {
    f: &'a Path,
    s: (usize, usize),
    e: (usize, usize),
}

impl<'a> Display for Location<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
	if self.s.0 == self.e.0 {
	    write!(f, "{}:{}.{}-{}", self.f.display(), self.s.0, self.s.1, self.e.1)
	} else {
	    write!(f, "{}:{}.{}-{}.{}", self.f.display(), self.s.0, self.s.1, self.e.0, self.e.1)
	}
    }
}

pub(crate) struct Located<'a, T>(pub(crate) Location<'a>, pub(crate) T);

impl<'a, T> Located<'a, T> {
    pub(crate) fn map<F, U>(self, f: F) -> Located<'a, U>
    where F: Fn(T) -> U
    {
	Located(self.0, f(self.1))
    }

    pub(crate) fn raw(self) -> T {
	self.1
    }

    pub(crate) fn loc(&self) -> Location<'a> {
	self.0
    }
}
