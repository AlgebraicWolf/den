use std::fmt::Display;

#[derive(Clone, Debug)]
/// Definition of an untyped lambda term, with bound names ranging over type [`T`]
pub enum Term<T> {
    /// A reference to some bound value
    Var(T),
    /// A lambda-abstraction binding some name
    Lam(T, Box<Term<T>>),
    /// An application of one term to another
    App(Box<Term<T>>, Box<Term<T>>),
    /// A let-binding, introducing some name into the context
    Let(T, Box<Term<T>>, Box<Term<T>>),
}

impl<T> Term<T> {
    pub fn is_lam(&self) -> bool {
        match self {
            Term::Lam(_, _) => true,
            _ => false,
        }
    }

    fn is_app(&self) -> bool {
        match self {
            Term::App(_, _) => true,
            _ => false,
        }
    }

    fn is_let(&self) -> bool {
        match self {
            Term::Let(_, _, _) => true,
            _ => false,
        }
    }

    /// Check if term is in normal form
    pub fn is_nf(&self) -> bool {
        // A term is a normal form if...
        match self {
            // If it is a free-standing variable, it is in NF
            Term::Var(_) => true,
            // If it is a lambda-abstraction, it's body should be in NF
            Term::Lam(_, term) => term.is_nf(),
            // If it is an application, left-hand side shouldn't be a lambda-abstraction,
            // and right-hand side should be in normal form
            Term::App(term, term1) => term.is_nf() && term1.is_nf() && !term.is_lam(),
            // "Let"-expression cannot occur in normal form
            Term::Let(_, _, _) => false,
        }
    }

    /// Transform the name representation
    pub fn map<F, U>(self, f: &F) -> Term<U>
    where
        F: Fn(T) -> U,
    {
        match self {
            Term::Var(n) => Term::Var(f(n)),
            Term::Lam(n, term) => Term::Lam(f(n), Box::new(term.map(f))),
            Term::App(term, term1) => Term::App(Box::new(term.map(f)), Box::new(term1.map(f))),
            Term::Let(n, term, term1) => {
                Term::Let(f(n), Box::new(term.map(f)), Box::new(term1.map(f)))
            }
        }
    }
}

impl<T> Display for Term<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(name) => write!(f, "{}", name),
            Term::Lam(name, term) => write!(f, "\\{} . {}", name, term),
            Term::App(term1, term2) => {
                if term1.is_lam() || term1.is_let() {
                    write!(f, "({})", term1)?;
                } else {
                    write!(f, "{}", term1)?;
                };

                if term2.is_app() || term2.is_lam() {
                    write!(f, " ({})", term2)?;
                } else {
                    write!(f, " {}", term2)?;
                }

                Ok(())
            }
            Term::Let(name, term, term1) => write!(f, "let {} = {}; {}", name, term, term1),
        }
    }
}
