use self::{
    env::{Env, GEnv, LEnv},
    value::{Function, Value},
};
use crate::parser::ast::*;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

mod env;
pub mod value;

impl Block {
    // Interprétation d'un bloc
    fn interp<'ast, 'genv>(&'ast self, env: &mut Env<'ast, 'genv>) -> Value<'ast> {
        let values = self.locals.iter().map(|_| Value::Nil);
        let new_env = &mut Env {
            locals: env.locals.extend(&self.locals, values),
            globals: env.globals,
        };
        let instrs = &self.body;
        instrs.interp(new_env);
        self.ret.interp(new_env)
    }
}

impl Stat_ {
    // Interprétation d'une instruction
    fn interp<'ast, 'genv>(&'ast self, env: &mut Env<'ast, 'genv>) {
        use Stat_::*;
        match self {
            Nop => (),
            Assign(Var::Name(name), exp) => {
                let v = exp.interp(env);
                env.set(name, v)
            }
            Assign(Var::IndexTable(exp1, exp2), exp) => {
                let t = exp1.interp(env).as_table();
                let k = exp2.interp(env).as_table_key();
                let v = exp.interp(env);
                (*t).borrow_mut().insert(k, v);
            }
            Seq(stat1, stat2) => {
                stat1.interp(env);
                stat2.interp(env);
            }
            StatFunctionCall(call) => {
                call.interp(env);
            }
            WhileDoEnd(exp, block) => {
                while exp.interp(env).as_bool() {
                    block.interp(env);
                }
            }
            If(exp, block1, block2) => {
                if exp.interp(env).as_bool() {
                    block1.interp(env);
                } else {
                    block2.interp(env);
                }
            }
        }
    }
}

impl FunctionCall {
    // Interprétation d'un appel de fonction
    fn interp<'ast, 'genv>(&'ast self, env: &mut Env<'ast, 'genv>) -> Value<'ast> {
        let FunctionCall(exp, args) = self;
        let v = exp.interp(env).as_function();
        match v {
            Function::Print => {
                let str = args
                    .iter()
                    .map(|arg| arg.interp(env).to_string())
                    .collect::<Vec<String>>();
                println!("{}", str.join("\t"));
                Value::Nil
            }
            Function::Closure(params, closure, block) => {
                let values = args.iter().map(|arg| arg.interp(env));
                let new_env = &mut Env {
                    locals: closure.extend(params, values),
                    globals: env.globals,
                };
                block.interp(new_env)
            }
        }
    }
}

impl Exp_ {
    // Interprétation d'une expression
    fn interp<'ast, 'genv>(&'ast self, env: &mut Env<'ast, 'genv>) -> Value<'ast> {
        match self {
            Exp_::Nil => Value::Nil,
            Exp_::False => Value::Bool(false),
            Exp_::True => Value::Bool(true),
            Exp_::Number(n) => Value::Number(*n),
            Exp_::LiteralString(s) => Value::String(s.clone()),
            Exp_::FunctionDef(body) => {
                let (args, block) = body;
                Value::Function(Function::Closure(args, Rc::clone(&env.locals), block))
            }
            Exp_::Var(name) => match name {
                Var::Name(n) => env.lookup(n),
                Var::IndexTable(exp1, exp2) => {
                    let v1 = exp1.interp(env);
                    let v2 = exp2.interp(env);
                    let t = Value::as_table(v1);
                    let table = (*t).borrow_mut();
                    match table.get(&v2.as_table_key()) {
                        Some(v) => v.clone(),
                        None => Value::Nil,
                    }
                }
            },
            Exp_::ExpFunctionCall(call) => call.interp(env),
            Exp_::BinOp(op, exp1, exp2) => {
                let v1 = exp1.interp(env);
                match op {
                    BinOp::Addition => v1.add(exp2.interp(env)),
                    BinOp::Subtraction => v1.sub(exp2.interp(env)),
                    BinOp::Multiplication => v1.mul(exp2.interp(env)),
                    BinOp::Less => Value::Bool(v1.lt(exp2.interp(env))),
                    BinOp::LessEq => Value::Bool(v1.le(exp2.interp(env))),
                    BinOp::Greater => Value::Bool((exp2.interp(env)).lt(v1)),
                    BinOp::GreaterEq => Value::Bool((exp2.interp(env)).le(v1)),
                    BinOp::Equality => Value::Bool(v1.eq(&exp2.interp(env))),
                    BinOp::Inequality => Value::Bool(!v1.eq(&exp2.interp(env))),
                    BinOp::LogicalAnd => {
                        if v1.as_bool() {
                            exp2.interp(env)
                        } else {
                            v1
                        }
                    }
                    BinOp::LogicalOr => {
                        if v1.as_bool() {
                            v1
                        } else {
                            exp2.interp(env)
                        }
                    }
                }
            }
            Exp_::UnOp(op, exp) => {
                let v = exp.interp(env);
                match op {
                    UnOp::Not => Value::Bool(!v.as_bool()),
                    UnOp::UnaryMinus => v.neg(),
                }
            }
            Exp_::Table(constr) => {
                let mut table = HashMap::new();
                for (key, value) in constr {
                    let k = key.interp(env).as_table_key();
                    let v = value.interp(env);
                    table.insert(k, v);
                }
                Value::Table(Rc::new(RefCell::new(table)))
            }
        }
    }
}

// Point d'entrée principal de l'interpréteur
pub fn run(ast: &Block) {
    let mut globals = GEnv(HashMap::new());
    let printid = "print".to_owned();
    globals.0.insert(&printid, Value::Function(Function::Print));
    let mut env = Env {
        locals: Rc::new(LEnv::Nil),
        globals: &mut globals,
    };
    ast.interp(&mut env);
}
