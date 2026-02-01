use std::{collections::HashMap, ops::RangeFrom};

use crate::{
    expr::{Expr, LocExprTP0},
    stmnt::SumConstructorList,
    types::Type0,
};

#[derive(Debug, Clone)]
pub(crate) enum TCError {
    HeteroPrim(Type0, Type0),
    TupleSizeError(usize, usize),
    WrongADT(usize, usize),
}

type Result<T> = std::result::Result<T, TCError>;

struct TypeChecker<'a> {
    vg: RangeFrom<usize>,
    bindings: HashMap<String, Type0>,
    eqs: Vec<(Type0, Type0)>,
    subst: HashMap<Type0, Type0>,

    sconstr: &'a SumConstructorList,
}

impl<'a> TypeChecker<'a> {
    fn init(constr: &'a SumConstructorList) -> Self {
        let mut bindings = HashMap::new();

        // TODO: fill primitive bindings

        Self {
            vg: (0..),
            bindings,
            eqs: vec![],
            subst: HashMap::new(),

            sconstr: constr,
        }
    }

    fn new_var(&mut self) -> usize {
        self.vg.next().unwrap()
    }

    fn add_eq(&mut self, lhs: Type0, rhs: Type0) {
        self.eqs.push((lhs, rhs));
    }

    fn unify(&mut self) -> Result<()> {
        todo!();
    }

    fn annotate(&mut self, e: LocExprTP0) -> LocExprTP0 {
        e.map(|e| match e {
            (_, Some(_)) => e,
            (x, None) => (x, Some(Type0::Var(self.new_var()))),
        })
    }

    fn check(&mut self, e: LocExprTP0) -> Result<()> {
        let ExprTP0(e, t) = e;

        match (e, t) {
            (_, None) => unreachable!(),
            (Expr::Char(_), Some(Type0::Char)) => Ok(()),
            (Expr::Char(_), Some(Type0::Var(i))) => {
                self.add_eq(Type0::Char, Type0::Var(i));

                self.unify()
            }
            (Expr::Char(_), Some(x)) => Err(TCError::HeteroPrim(Type0::Char, x)),
            (Expr::Int(_), Some(Type0::Int)) => Ok(()),
            (Expr::Int(_), Some(Type0::Var(i))) => {
                self.add_eq(Type0::Int, Type0::Var(i));

                self.unify()
            }
            (Expr::Int(_), Some(x)) => Err(TCError::HeteroPrim(Type0::Int, x)),
            (Expr::Float(_), Some(Type0::Float)) => Ok(()),
            (Expr::Float(_), Some(Type0::Var(i))) => {
                self.add_eq(Type0::Float, Type0::Var(i));

                self.unify()
            }
            (Expr::Float(_), Some(x)) => Err(TCError::HeteroPrim(Type0::Float, x)),
            (Expr::Tuple(args), Some(Type0::Tuple(targs))) => {
                if args.len() != targs.len() {
                    Err(TCError::TupleSizeError(args.len(), targs.len()))
                } else {
                    for (box arg, targ) in args.into_iter().zip(targs.into_iter()) {
                        let arga = self.annotate(arg);

                        self.check(arga.clone())
                            .and(self.check(ExprTP0(arga.0, Some(targ))))?;
                    }

                    Ok(())
                }
            }
            (Expr::Tuple(args), Some(Type0::Var(i))) => {
                let targs = args
                    .into_iter()
                    .map(|x| self.annotate(x).1)
                    .filter_map(|x| x)
                    .collect();

                self.add_eq(Type0::Tuple(targs), Type0::Var(i));

                self.unify()
            }
            (Expr::Tuple(args), Some(x)) => Err(TCError::HeteroPrim(
                Type0::Tuple(
                    args.into_iter()
                        .enumerate()
                        .map(|x| Type0::Var(x.0))
                        .collect(),
                ),
                x,
            )),

            (Expr::Binding(s), Some(x)) => {
                let y = &self.bindings[&s];

                if &x != y {
                    self.add_eq(x, y.clone());
                }

                self.unify()
            }

            (Expr::Const(ci, args), Some(Type0::Data(ti, targs))) => {
                let k = self.sconstr[ci];

                if k.adt != ti {
                    Err(TCError::WrongADT(k.adt, ti))
                } else {
                    for (box arg, t) in args.into_iter().zip(k.targs.iter()) {
                        let t = resolve_constr_type(t, &targs);
                        let arga = self.annotate(arg);

                        self.check(arga.clone())
                            .and(self.check(ExprTP0(arga.0, Some(t))))?;
                    }

                    Ok(())
                }
            }
            (Expr::Const(ci, args), Some(Type0::Var(i))) => {
                let k = self.sconstr[ci];

                for (box arg, t) in args.into_iter().zip(k.targs.iter()) {
                    todo!()
                }

                Ok(())
            }
        }
    }
}

fn resolve_constr_type(t: &Type0, targs: &[Type0]) -> Type0 {
    match t {
        Type0::Bool | Type0::Char | Type0::Int | Type0::Float => t.clone(),
        Type0::Tuple(ts) => {
            Type0::Tuple(ts.iter().map(|x| resolve_constr_type(x, targs)).collect())
        }
        Type0::Fn(args, ret) => {
            let args = args.iter().map(|x| resolve_constr_type(x, targs)).collect();
            let ret = resolve_constr_type(ret, targs);

            Type0::Fn(args, Box::new(ret))
        }
        Type0::Var(i) => targs[*i].clone(),
        Type0::Data(i, args) => Type0::Data(
            *i,
            args.iter().map(|x| resolve_constr_type(x, targs)).collect(),
        ),
    }
}
