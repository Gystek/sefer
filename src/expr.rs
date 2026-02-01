use crate::{location::{Wrapper, Located}, pattern::LocPattern, types::Type0};

#[derive(Debug, Clone)]
pub(crate) enum Expr<P, T> {
    Char(char),
    Int(i64),
    Float(f64),
    Bool(bool),
    Tuple(Vec<T>),

    Binding(String),

    Const(usize, Vec<T>),

    App(T, Vec<T>),
    Abs(Vec<String>, T),

    // let 0 = 1 in 2
    Let(String, T, T),
    Cond(T, T, T),

    // match 0 with 1.0 if 1.1 -> 1.2
    Match(T, Vec<(P, T, T)>),
}

#[derive(Debug, Clone)]
pub(crate) struct LocExprTP0<'a>(
    pub(crate) Located<'a, (Expr<LocPattern<'a>, Box<LocExprTP0<'a>>>, Option<Type0>)>,
);

impl<'a> LocExprTP0<'a> {
    pub(crate) fn map<F>(self, f: F) -> Self
    where
        F: Fn(
            (Expr<LocPattern<'a>, Box<LocExprTP0<'a>>>, Option<Type0>),
        ) -> (Expr<LocPattern<'a>, Box<LocExprTP0<'a>>>, Option<Type0>),
    {
        LocExprTP0(self.0.map(f))
    }
}

#[derive(Debug, Clone)]
pub(crate) struct LocExprTF0<'a>(
    pub(crate) Located<'a, (Expr<LocPattern<'a>, Box<LocExprTF0<'a>>>, Type0)>,
);

impl<'a> LocExprTF0<'a> {
    pub(crate) fn map<F>(self, f: F) -> Self
    where
        F: Fn(
            (Expr<LocPattern<'a>, Box<LocExprTP0<'a>>>, Option<Type0>),
        ) -> (Expr<LocPattern<'a>, Box<LocExprTP0<'a>>>, Option<Type0>),
    {
        LocExprTF0(self.0.map(f))
    }
}
