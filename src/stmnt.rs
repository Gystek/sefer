use crate::types::Type0;

#[derive(Debug, Clone)]
pub(crate) struct ADType {
    vars: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct SumConstructor {
    // index of the parent datatype
    pub(crate) adt: usize,
    // type variables are numbered from 0 onwards
    // apart from (parent-inherited) type variables, all variables
    // here are concrete
    pub(crate) targs: Vec<Type0>,
}

pub(crate) type ADTypeList = Vec<ADType>;
pub(crate) type SumConstructorList = Vec<SumConstructor>;
