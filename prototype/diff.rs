// The parser (badly) written here recognizes the following language (and also computes
// the value of the given operations):
//   S -> E
//   E -> E '-' T
//   E -> T
//   T -> ('0'..'9')+
//   T -> '(' E ')'
//
// This is a non-LR(0) grammar. This program is (perhaps unneeded) proof that non-LR(0)
// languages can be parsed by non-peekable iterators.
//
// My use of `Vec` here is purely for performance reasons, it can be directly swapped
// for a linked list.
//
// I apologise for the code quality, but it wasn't the point at the time of writing.
#![feature(box_patterns)]
use std::io::{self, BufRead};

#[derive(Debug, Clone)]
enum Expr {
    Sub(Box<Expr>, Box<Expr>),
    Term(i32)
}

impl Expr {
    fn compute(self) -> i32 {
        match self {
            Self::Sub(box x, box y) => x.compute() - y.compute(),
            Self::Term(x) => x,
        }
    }
}

#[derive(Debug, Clone)]
enum State {
    Minus(Expr), // left hand side
    Number(i32),
    Expr(Expr),
    Paren,
    Start
}

fn subst(s: &str) -> i32 {
    let ss = s
        .chars()
        .filter(|&x| x != ' ')
        .fold(vec![State::Start], |mut s, x| {
            let l = s[s.len() - 1].clone();
 
            match x {
                '0' | '1' | '2' | '3' | '4' |
                '5' | '6' | '7' | '8' | '9' => match l {
                    State::Number(i) => {
                        let il = s.len() - 1;
                        s[il] = State::Number(i * 10 + x.to_digit(10).unwrap() as i32);
                        s
                    }
                    State::Start => {
                    let il = s.len() - 1;
                        s[il] = State::Number(x.to_digit(10).unwrap() as i32);
                        s
                    },
                    State::Minus(_) | State::Paren => {
                        s.push(State::Number(x.to_digit(10).unwrap() as i32));
                        s
                    }
                    State::Expr(_) => panic!("an expression cannot follow another expression"),
                    
                }
                '(' => {
                    s.push(State::Paren);
                    s
                }
                ')' => match l {
                    State::Paren => panic!("`()` is invalid"),
                    State::Start => panic!("`)` without `(`"),
                    State::Minus(_) => panic!("`-)` is invalid"),
                    State::Expr(f) => {
                        s.pop();
                        let il = s.len() - 1;
                        let l = s[il].clone();
                        
                        match l {
                            State::Minus(e) => {
                                let e = Expr::Sub(Box::new(e), Box::new(f));
                                s.pop();
                                s.push(State::Expr(e));
                                s
                            }
                            State::Paren => {
                                s.pop();
                                s.push(State::Expr(f));
                                s
                            }
                            State::Start => panic!("`<x>)` is invalid"),
                            _ => unreachable!(),
                        }
                    }
                    State::Number(i) => {
                        let f = Expr::Term(i);
                        s.pop();
                        let il = s.len() - 1;
                        let l = s[il].clone();
                        
                        match l {
                            State::Minus(e) => {
                                let e = Expr::Sub(Box::new(e), Box::new(f));
                                s.pop();
                                let il = s.len() - 1;
                                let l = s[il].clone();
                                
                                s.push(State::Expr(e));
                                s
                            }
                            State::Paren => {
                                s.pop();
                                s.push(State::Expr(f));
                                s
                            }
                            State::Start => panic!("`<x>)` is invalid"),
                            _ => unreachable!(),
                        }
                    }
                }
                '-' => match l {
                    State::Minus(_) => panic!("`<x> - -` is invalid"),
                    State::Number(i) => {
                        let f = Expr::Term(i);
                        s.pop();
                        
                        if !s.is_empty() {
                            let il = s.len() - 1;
                            let l = s[il].clone();

                            s[il] = State::Minus(match l {
                                State::Minus(e) => Expr::Sub(Box::new(e), Box::new(f)),
                                _ => f,
                            });
                        } else {
                            s.push(State::Minus(f));
                        }
                        s
                    }
                    State::Expr(f) => {
                        s.pop();
                        if !s.is_empty() {
                            let il = s.len() - 1;
                            let l = s[il].clone();

                            s[il] = State::Minus(match l {
                                State::Minus(e) => Expr::Sub(Box::new(e), Box::new(f)),
                                _ => f,
                            });
                        } else {
                            s.push(State::Minus(f));
                        }
                        s
                    }
                    State::Start => panic!("`-` at the start of expression"),
                    State::Paren => panic!("`(-` is invalid"),
                    
                }
                _ => panic!("`{x}` is not a valid lexical element"),
            }
        })
        .into_iter()
        .filter(|x| match x {
            State::Start => false,
            _ => true,
        })
        .collect::<Vec<State>>();
        
    if ss.len() == 1 {
        match &ss[0] {
            State::Start => 0,
            State::Expr(e) => e.clone().compute(),
            State::Number(i) => *i,
            x => panic!("unexpected final element: {x:?}"),
        }
    } else if ss.len() == 2 {
        match (&ss[0], &ss[1]) {
            (State::Minus(e), State::Expr(f)) => {
                Expr::Sub(Box::new(e.clone()), Box::new(f.clone())).compute()
            }
            (State::Minus(e), State::Number(i)) => {
                e.clone().compute() - *i
            }
            (x, y) => panic!("unexpected final two elements, {x:?} and {y:?}"),
        }
    } else {
        panic!("invalid final state: {ss:?}");
    }
}

fn main() {
    let stdin = io::stdin();
    
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let x = subst(&line.trim());
        println!("{} = {}", line.trim(), x);
    }
}
