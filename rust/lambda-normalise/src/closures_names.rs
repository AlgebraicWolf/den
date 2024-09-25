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
    /// Apply a value to a closure. The value is delayed, because it might
    /// diverge, yet the closure might not use its argument in any 
    /// meaningful way.
    fn app(&self, val: Lazy<'a, Value<'a, T>>) -> Value<'a, T> {
        let mut env = self.env.clone();
        env.insert(self.name.clone(), val);
        eval(env, self.body.clone())
    }
}

/// Values that lambda-terms are evaluated into, with names ranging over type [`T`].
#[derive(Clone)]
enum Value<'a, T> {
    /// Refernce to some name.
    VVar(T),
    /// Application of one name to another.
    VApp(Box<Value<'a, T>>, Lazy<'a, Value<'a, T>>),
    /// Lambda-abstraction.
    VLam(Closure<'a, T>),
}

impl<'a, T> Value<'a, T> {
    /// Application of one term to another. The argument is delayed, because
    /// it might diverge.
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

/// Evaluate a lambda term in the environment, and obtain some value as a result.
fn eval<'a, T>(env: HashMap<T, Lazy<'a, Value<'a, T>>>, tm: Term<T>) -> Value<'a, T>
where
    T: Clone + Eq + Hash + 'a,
{
    match tm {
        // If the term is a name, we check if there is a bound value.
        Term::Var(nm) => match env.get(&nm) {
            // If there is, we force its evaluation
            Some(v) => v(),
            // If there is none, the variable is free, and we leave it be.
            None => Value::VVar(nm),
        },
        // If the term is a lambda, we turn it into a closure.
        Term::Lam(name, body) => Value::VLam(Closure {
            name,
            env,
            body: *body,
        }),
        // If the term is an application, we evaluate the function,
        // and apply the delayed argument.
        Term::App(term, term1) => {
            eval(env.clone(), *term).app(Rc::new(move || eval(env.clone(), *term1.clone())))
        }
        // If the term is a let binding, we evaluate the bound expression,
        // add it to context and evaluate the body.
        Term::Let(name, term, term1) => {
            let mut env_ = env.clone();
            env_.insert(name, Rc::new(move || eval(env.clone(), *term.clone())));
            eval(env_, *term1)
        }
    }
}

/// Take a value back into a world of terms.
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

/// Normalise the term by evaluating it and then turning the value back
/// into a term.
pub fn normalise<T>(term: Term<T>) -> Term<T>
where
    T: Fresh + Clone + Eq + Hash,
{
    quote(&mut HashMap::new(), eval(HashMap::new(), term))
}
