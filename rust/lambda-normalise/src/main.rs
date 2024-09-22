#![feature(box_patterns)]

use std::{collections::HashMap, fmt::Display, io::Read, process::exit, str::from_utf8};

use parser::{parse_tokenised, tokenise, TokenSeq};
use term::Term;

mod fresh;
mod hoas_names;
mod parser;
mod reductions;
mod term;

#[derive(PartialEq, Eq, Hash, Clone)]
enum Name<'a> {
    FromSource(&'a str),
    Fresh(&'a str, u64),
}

struct Mode {
    name: &'static str,
    description: &'static str,
    handler: Box<dyn Fn(Term<Name>) -> Term<Name>>,
}

impl<'a> fresh::Fresh for Name<'a> {
    fn fresh_in_env<T>(&self, env: &HashMap<Self, T>) -> Self {
        if !env.contains_key(self) {
            return self.clone();
        }

        let base = match self {
            Name::FromSource(s) => s,
            Name::Fresh(s, _) => s,
        };
        let mut index = match self {
            Name::FromSource(_) => 0,
            Name::Fresh(_, i) => i + 1,
        };

        while env.contains_key(&Name::Fresh(base, index)) {
            index += 1;
        }

        Name::Fresh(base, index)
    }
}

impl<'a> Display for Name<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Name::FromSource(s) => write!(f, "{}", s),
            Name::Fresh(s, i) => write!(f, "{}{}", s, i),
        }
    }
}

fn print_modes(modes: &[Mode]) {
    println!("Available modes:");

    for mode in modes {
        println!("\t{}:\t{}", mode.name, mode.description);
    }
}

fn run_mode<'a>(m: &Mode, prog: &'a str) -> Result<Term<Name<'a>>, String> {
    let (_, tokens) = tokenise(prog).map_err(|e| format!("Error during tokenisation: {}", e))?;
    let (_, term) =
        parse_tokenised(TokenSeq(&tokens)).map_err(|e| format!("Error during parsing: {}", e))?;
    Ok((m.handler)(term.map(&Name::FromSource)))
}

fn main() {
    let modes = [
        Mode {
            name: "rewrite",
            description: "syntatic rewrite-based normalisation algorithm",
            handler: Box::new(|t| reductions::normalise(t)),
        },
        Mode {
            name: "hoas-names",
            description: "NbE normalisation algorithm, encoding lambdas using HOAS",
            handler: Box::new(|t| hoas_names::normalise(t)),
        },
    ];

    let mut args = std::env::args();
    let Some(exec_name) = args.next() else {
        panic!("Invariant violation: at least one arg must always be present");
    };
    let mode = args.next();
    let mode = match mode {
        Some(mode) if mode != "--help" => mode,
        _ => {
            println!("Usage:");
            println!("\t{} [MODE]", exec_name);
            println!("");

            print_modes(&modes);
            exit(0);
        }
    };

    for m in modes.iter() {
        if m.name == mode {
            let mut term_raw = vec![];
            std::io::stdin().lock().read_to_end(&mut term_raw).unwrap();
            let norm = run_mode(m, from_utf8(term_raw.as_slice()).unwrap()).unwrap();
            println!("Normalised: {}", norm);
            exit(0);
        }
    }

    print!("No mode \"{}\". ", mode);
    print_modes(&modes);
    exit(1);
}
