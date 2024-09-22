use std::{
    iter::{Cloned, Enumerate},
    slice::Iter,
};

use nom::{
    branch::alt,
    bytes::complete::{tag, tag_no_case},
    character::complete::{alphanumeric1, char, multispace0},
    combinator::{all_consuming, value},
    error::Error,
    multi::{many0, many1},
    sequence::{delimited, preceded},
    Compare, Err, IResult, InputIter, InputLength, InputTake, Needed,
};

use crate::term::Term;

#[derive(Clone, PartialEq, Eq, Debug)]
/// A token, with identifiers ranging over type [`T`]
pub enum Token<T> {
    LParen,
    RParen,
    Lam,
    Dot,
    Let,
    Assign,
    Semicolon,
    Ident(T),
}

#[derive(Clone, PartialEq, Eq, Debug)]
/// A sequence of tokens.
/// The newtype is required to implement some necessary traits.
pub struct TokenSeq<'a, T>(pub &'a [Token<T>]);

impl<'a, T> InputTake for TokenSeq<'a, T> {
    fn take(&self, count: usize) -> Self {
        TokenSeq(&self.0[0..count])
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        let (prefix, suffix) = self.0.split_at(count);
        (TokenSeq(suffix), TokenSeq(prefix))
    }
}

impl<'a, T> InputLength for TokenSeq<'a, T> {
    fn input_len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, 'b, T> Compare<TokenSeq<'b, T>> for TokenSeq<'a, T>
where
    T: PartialEq,
{
    fn compare(&self, t: TokenSeq<'b, T>) -> nom::CompareResult {
        match self.0.iter().zip(t.0.iter()).position(|(a, b)| a != b) {
            Some(_) => nom::CompareResult::Error,
            None => {
                if self.0.len() >= t.0.len() {
                    nom::CompareResult::Ok
                } else {
                    nom::CompareResult::Incomplete
                }
            }
        }
    }

    fn compare_no_case(&self, t: TokenSeq<'b, T>) -> nom::CompareResult {
        self.compare(t)
    }
}

impl<'a, T> InputIter for TokenSeq<'a, T>
where
    T: Clone,
{
    type Item = Token<T>;

    type Iter = Enumerate<Self::IterElem>;

    type IterElem = Cloned<Iter<'a, Token<T>>>;

    fn iter_indices(&self) -> Self::Iter {
        self.iter_elements().enumerate()
    }

    fn iter_elements(&self) -> Self::IterElem {
        self.0.iter().cloned()
    }

    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.0.iter().position(|x| predicate(x.clone()))
    }

    fn slice_index(&self, count: usize) -> Result<usize, nom::Needed> {
        if self.0.len() >= count {
            Ok(count)
        } else {
            Err(Needed::new(count - self.0.len()))
        }
    }
}

fn tokenise_ident(input: &str) -> IResult<&str, Token<&str>> {
    let (remaining, ident) = alphanumeric1(input)?;
    Ok((remaining, Token::Ident(ident)))
}

fn tokenise_single(input: &str) -> IResult<&str, Token<&str>> {
    alt((
        value(Token::Lam, char('\\')),
        value(Token::Dot, char('.')),
        value(Token::LParen, char('(')),
        value(Token::RParen, char(')')),
        value(Token::Let, tag_no_case("let")),
        value(Token::Assign, char('=')),
        value(Token::Semicolon, char(';')),
        tokenise_ident,
    ))(input)
}

pub fn tokenise(s: &str) -> IResult<&str, Vec<Token<&str>>> {
    all_consuming(delimited(
        multispace0,
        many0(preceded(multispace0, tokenise_single)),
        multispace0,
    ))(s)
}

fn parse_name<T>(input: TokenSeq<T>) -> IResult<TokenSeq<T>, T>
where
    T: Clone,
{
    let Some((Token::Ident(name), remaining)) = input.0.split_first() else {
        return Err(Err::Error(Error::new(input, nom::error::ErrorKind::Fail)));
    };

    Ok((TokenSeq(remaining), name.clone()))
}

fn parse_name_list<T>(input: TokenSeq<T>) -> IResult<TokenSeq<T>, Vec<T>>
where
    T: Clone,
{
    many1(parse_name)(input)
}

fn parse_lambda_abstraction<T>(input: TokenSeq<T>) -> IResult<TokenSeq<T>, Term<T>>
where
    T: PartialEq + Clone,
{
    // Parse the head of lambda abstraction
    let (remaining, bound) = preceded(tag(TokenSeq(&[Token::Lam])), parse_name_list)(input)?;
    // Parse the body of lambda abstraction
    let (remaining, body) = preceded(tag(TokenSeq(&[Token::Dot])), parse_tokenised)(remaining)?;

    // Apply all the binders
    let mut term = body;
    for name in bound.into_iter().rev() {
        term = Term::Lam(name, Box::new(term));
    }

    Ok((remaining, term))
}

fn parse_let_binding<T>(input: TokenSeq<T>) -> IResult<TokenSeq<T>, Term<T>>
where
    T: PartialEq + Clone,
{
    let (remaining, bound) = preceded(tag(TokenSeq(&[Token::Let])), parse_name)(input)?;
    let (remaining, term) = preceded(tag(TokenSeq(&[Token::Assign])), parse_tokenised)(remaining)?;
    let (remaining, term1) =
        preceded(tag(TokenSeq(&[Token::Semicolon])), parse_tokenised)(remaining)?;
    Ok((remaining, Term::Let(bound, Box::new(term), Box::new(term1))))
}

fn parse_applications<T>(input: TokenSeq<T>) -> IResult<TokenSeq<T>, Term<T>>
where
    T: PartialEq + Clone,
{
    let (remaining, mut term) = parse_tokenised_noapp(input)?;
    let (remaining, args) = many0(parse_tokenised_noapp)(remaining)?;

    for arg in args.into_iter() {
        term = Term::App(Box::new(term), Box::new(arg));
    }

    Ok((remaining, term))
}

fn parse_var<T>(input: TokenSeq<T>) -> IResult<TokenSeq<T>, Term<T>>
where
    T: Clone,
{
    let (remaining, name) = parse_name(input)?;
    Ok((remaining, Term::Var(name)))
}

fn parse_tokenised_noapp<T>(input: TokenSeq<T>) -> IResult<TokenSeq<T>, Term<T>>
where
    T: PartialEq + Clone,
{
    alt((
        // Recursively, a parenthesized equation
        delimited(
            tag(TokenSeq(&[Token::LParen])),
            parse_tokenised,
            tag(TokenSeq(&[Token::RParen])),
        ),
        // Try to parse a lambda-abstraction
        parse_lambda_abstraction,
        // Try to parse a let-binding
        parse_let_binding,
        // Try to parse an application
        // parse_applications,
        // Try to parse a var reference
        parse_var,
    ))(input)
}

pub fn parse_tokenised<T>(input: TokenSeq<T>) -> IResult<TokenSeq<T>, Term<T>>
where
    T: PartialEq + Clone,
{
    parse_applications(input)
}
