#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Type0 {
    Char,
    Int,
    Float,
    Bool,

    Var(usize),

    Fn(Vec<Type0>, Box<Type0>),

    // data T a b = ...
    //
    // T Int Int = Constr(0, [Int, Int])
    Data(usize, Vec<Type0>),

    Tuple(Vec<Type0>),
}
