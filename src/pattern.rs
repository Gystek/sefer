use crate::location::Located;

#[derive(Debug, Clone)]
pub(crate) enum Pattern<T> {
    Const(usize, Vec<T>),
    Tuple(Vec<T>),
    Binding(String),

    Char(char),
    Int(i64),
    Float(f64),
    Bool(bool),
}

#[derive(Debug, Clone)]
pub(crate) struct LocPattern<'a>(pub(crate) Located<'a, Pattern<LocPattern<'a>>>);
