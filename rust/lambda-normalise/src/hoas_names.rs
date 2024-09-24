use std::{collections::HashMap, hash::Hash, rc::Rc};

use crate::fresh::Fresh;

use super::term::Term;

type Lazy<'a, T> = Rc<dyn Fn() -> T + 'a>;

/// Values that lambda terms are evaluated into. Names are stored internally,
/// and are ranging over the type [`T`]
#[derive(Clone)]
enum Value<'a, T> {
    /// Some bound variable.
    VVar(T),
    /// "Stuck" application that cannot be further reduced yet.
    /// Note that the right-hand side is delayed.
    VApp(Box<Value<'a, T>>, Lazy<'a, Value<'a, T>>),
    /// Lambda abstraction. Note that it accepts a delayed value.
    VLam(T, Rc<dyn Fn(Lazy<'a, Value<'a, T>>) -> Value<'a, T> + 'a>),
}

impl<'a, T> Value<'a, T> {
    /// Evaluation of application. Performs beta-reduction if lhs is a lambda abstraction.
    /// Produces stuck term otherwise.
    fn app(self, v: Lazy<'a, Self>) -> Self {
        match self {
            Value::VLam(_, f) => f(v),
            _ => Value::VApp(Box::new(self), v),
        }
    }
}

/// Evaluate a term into a value. The resulting value will be in a normal form.
fn eval<'a, T>(env: HashMap<T, Lazy<'a, Value<'a, T>>>, tm: Term<T>) -> Value<'a, T>
where
    T: Eq + Hash + Clone + 'a,
{
    // By cases on the term construction...
    match tm {
        // If term is a variable reference, check if it is present in the context...
        Term::Var(n) => match env.get(&n) {
            // If it is, pull the value from the context.
            // At this point, we force the evaluation.
            Some(v) => v(),
            // If it is not, this means that it is some external irreducible name.
            // Leave it be as it is.
            None => Value::VVar(n),
        },
        // If it is a lambda-abstraction, evaluate its body.
        Term::Lam(nm, term) => Value::VLam(
            nm.clone(),
            Rc::new(move |v| {
                let mut env = env.clone();
                env.insert(nm.clone(), v);
                eval(env, *term.clone())
            }),
        ),
        // If it is an application, evaluate the left-hand side and apply
        // (lazily evaluated) right-hand side.
        Term::App(term, term1) => {
            eval(env.clone(), *term).app(Rc::new(move || eval(env.clone(), *term1.clone())))
        }
        // If it is a let binding, add the bound name with a value to the context, and evaluate the term.
        Term::Let(nm, term, term1) => {
            let mut env_ = env.clone();
            env_.insert(
                nm.clone(),
                Rc::new(move || eval(env.clone(), *term.clone())),
            );
            eval(env_, *term1)
        }
    }
}

/// Guide a value back into a world of terms, carefully keeping
/// track of current namespace and cleaning up any confusion.
fn quote<'a, T>(v: Value<'a, T>, ns: &mut HashMap<T, ()>) -> Term<T>
where
    T: Clone + Fresh + Eq + Hash + 'a,
{
    match v {
        Value::VVar(n) => Term::Var(n),
        Value::VApp(value, f) => Term::App(
            Box::new(quote(*value, &mut ns.clone())),
            Box::new(quote(f(), ns)),
        ),
        Value::VLam(n, f) => {
            let n = n.fresh_in_env(ns);
            ns.insert(n.clone(), ());
            Term::Lam(
                n.clone(),
                Box::new(quote(f(Rc::new(move || Value::VVar(n.clone()))), ns)),
            )
        }
    }
}

/// Travel to the world of values and back, turning into the normal form.
pub fn normalise<T>(term: Term<T>) -> Term<T>
where
    T: Eq + Clone + Hash + Fresh,
{
    quote(eval(HashMap::new(), term), &mut HashMap::new())
}
