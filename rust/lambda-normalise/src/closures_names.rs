use std::hash::Hash;
use std::{collections::HashMap, rc::Rc};

use crate::fresh::Fresh;
use crate::term::Term;

type Lazy<'a, T> = Rc<dyn Fn() -> T + 'a>;

/// Name bound by a closure, along with some environment, and a
/// body of a closure, represented as a term.
#[derive(Clone)]
struct Closure<'a, T> {
    name: T,
    env: HashMap<T, Lazy<'a, Value<'a, T>>>,
    body: Term<T>,
}

impl<'a, T> Closure<'a, T>
where
    T: Clone + Hash + Eq + 'a,
{
    fn app(&self, val: Lazy<'a, Value<'a, T>>) -> Value<'a, T> {
        let mut env = self.env.clone();
        env.insert(self.name.clone(), val);
        eval(env, self.body.clone())
    }
}

#[derive(Clone)]
enum Value<'a, T> {
    VVar(T),
    VApp(Box<Value<'a, T>>, Lazy<'a, Value<'a, T>>),
    VLam(Closure<'a, T>),
}

impl<'a, T> Value<'a, T> {
    fn app(self, val: Lazy<'a, Value<'a, T>>) -> Value<'a, T>
    where
        T: Clone + Hash + Eq + 'a,
    {
        match self {
            Value::VLam(closure) => closure.app(val),
            f => Value::VApp(Box::new(f), val),
        }
    }
}

fn eval<'a, T>(env: HashMap<T, Lazy<'a, Value<'a, T>>>, tm: Term<T>) -> Value<'a, T>
where
    T: Clone + Eq + Hash + 'a,
{
    match tm {
        Term::Var(nm) => match env.get(&nm) {
            Some(v) => v(),
            None => Value::VVar(nm),
        },
        Term::Lam(name, body) => Value::VLam(Closure {
            name,
            env,
            body: *body,
        }),
        Term::App(term, term1) => {
            eval(env.clone(), *term).app(Rc::new(move || eval(env.clone(), *term1.clone())))
        }
        Term::Let(name, term, term1) => {
            let mut env_ = env.clone();
            env_.insert(name, Rc::new(move || eval(env.clone(), *term.clone())));
            eval(env_, *term1)
        }
    }
}

fn quote<'a, T>(ns: &mut HashMap<T, ()>, v: Value<'a, T>) -> Term<T>
where
    T: Fresh + Clone + Eq + Hash + 'a,
{
    match v {
        Value::VVar(nm) => Term::Var(nm),
        Value::VApp(f, arg) => Term::App(
            Box::new(quote(&mut ns.clone(), *f)),
            Box::new(quote(ns, arg())),
        ),
        Value::VLam(cl) => {
            let name = cl.name.fresh_in_env(ns);
            ns.insert(name.clone(), ());
            Term::Lam(
                name.clone(),
                Box::new(quote(
                    ns,
                    cl.app(Rc::new(move || Value::VVar(name.clone()))),
                )),
            )
        }
    }
}

pub fn normalise<T>(term: Term<T>) -> Term<T>
where
    T: Fresh + Clone + Eq + Hash,
{
    quote(&mut HashMap::new(), eval(HashMap::new(), term))
}
