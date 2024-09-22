use std::collections::HashMap;
use std::hash::Hash;

use crate::fresh::Fresh;

use super::term::Term;

/// Collect the "substantial" names, i. e. the names that occur in places other than just bindings.
/// This is a simpler-to-compute approximation of collecting names that occur freely.
fn gather_substantial_names<T>(term: &Term<T>, ns: &mut HashMap<T, ()>)
where
    T: Eq + Hash + Clone,
{
    match term {
        Term::Var(n) => {
            ns.insert(n.clone(), ());
        }
        Term::Lam(_, term) => {
            gather_substantial_names(term, ns);
        }
        Term::App(term, term1) => {
            gather_substantial_names(term, ns);
            gather_substantial_names(term1, ns);
        }
        Term::Let(_, term, term1) => {
            gather_substantial_names(term, ns);
            gather_substantial_names(term1, ns);
        }
    };
}

/// Replace any occurrence of a name with the smallest fresh name not
/// in the provided namespace. Note that it does not populate the namespace.
fn replace_names_with_fresh<T>(term: Term<T>, ns: &HashMap<T, ()>) -> Term<T>
where
    T: Fresh,
{
    match term {
        Term::Var(n) => Term::Var(n.fresh_in_env(ns)),
        Term::Lam(n, term) => Term::Lam(
            n.fresh_in_env(ns),
            Box::new(replace_names_with_fresh(*term, ns)),
        ),
        Term::App(term, term1) => Term::App(
            Box::new(replace_names_with_fresh(*term, ns)),
            Box::new(replace_names_with_fresh(*term1, ns)),
        ),
        Term::Let(n, term, term1) => Term::Let(
            n.fresh_in_env(ns),
            Box::new(replace_names_with_fresh(*term, ns)),
            Box::new(replace_names_with_fresh(*term1, ns)),
        ),
    }
}

fn subst<T>(n: &T, term: Term<T>, subterm: Term<T>) -> Term<T>
where
    T: Eq + Hash + Clone + Fresh,
{
    fn subst_internal<T>(n: &T, term: Term<T>, subterm: Term<T>) -> Term<T>
    where
        T: Eq + Hash + Clone,
    {
        match term {
            // If it's a variable reference, we check if the name matches.
            Term::Var(m) => {
                if *n == m {
                    subterm
                } else {
                    Term::Var(m)
                }
            }
            // Under a lambda, we proceed with substitution only
            // if the name DOES NOT MATCH.
            Term::Lam(m, term) => {
                if *n == m {
                    Term::Lam(m, term)
                } else {
                    Term::Lam(m, Box::new(subst_internal(n, *term, subterm)))
                }
            }
            // Recursively substitute in both parts of application
            Term::App(term, term1) => Term::App(
                Box::new(subst_internal(n, *term, subterm.clone())),
                Box::new(subst_internal(n, *term1, subterm)),
            ),
            // Like in case of a lambda, we substitute under let only if the name
            // does not match. However, here we perform substituton in the expression
            // binding the name regardless.
            Term::Let(m, term, term1) => {
                if *n == m {
                    Term::Let(m, Box::new(subst_internal(n, *term, subterm)), term1)
                } else {
                    Term::Let(
                        m,
                        Box::new(subst_internal(n, *term, subterm.clone())),
                        Box::new(subst_internal(n, *term1, subterm)),
                    )
                }
            }
        }
    }

    // Technically, it is sufficient to gather and substitute
    // only the free names in here. But gathering only the "substantial"
    // names, by which I mean the names that occur in places other than bindings
    // is easier and should work too.
    let mut ns = HashMap::new();
    gather_substantial_names(&subterm, &mut ns);
    let term = replace_names_with_fresh(term, &ns);

    subst_internal(n, term, subterm)
}

/// Perform a single reduction step, if possible
fn reduce_step<T>(term: Term<T>) -> Term<T>
where
    T: Eq + Hash + Clone + Fresh,
{
    match term {
        // Non-recursive cases: we can make a step right here
        // Application to a lambda-abstraction: we discard the lambda and
        // substitute the bound name in the body.
        Term::App(box Term::Lam(n, body), arg) => subst(&n, *body, *arg),
        // Let-pattern: we discard the let and substitute the expression in body.
        Term::Let(n, term, term1) => subst(&n, *term1, *term),
        // Recursive cases: the step is possible somewhere deeper
        // In app, we can reduce in left-hand side if it's not in NF.
        Term::App(term, term1) if !term.is_nf() => {
            Term::App(Box::new(reduce_step(*term)), term1)
        }
        // If left-hand side is in NF, then we can reduce in
        // right-hand side if it's not in NF. Note that by now we know that
        // the left-hand side is not lambda, otherwise the earlier case
        // would've been successful.
        Term::App(term, term1) if !term1.is_nf() => {
            Term::App(term, Box::new(reduce_step(*term1)))
        }
        // In lambda, the reduction might be possible in body
        Term::Lam(n, body) => {
            Term::Lam(n, Box::new(reduce_step(*body)))
        }

        // No substituon possible, return term as is
        term => term,
    }
}

/// Normalisation performs reduction steps as long as possible
pub fn normalise<T>(mut term: Term<T>) -> Term<T>
where
    T: Eq + Hash + Clone + Fresh,
{
    while !term.is_nf() {
        term = reduce_step(term);
    }

    term
}
