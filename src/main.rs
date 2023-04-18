use std::{
    cmp::Ordering,
    env,
    fmt,
    io::{self, Write as _},
    iter,
    num::ParseIntError,
    str,
    sync::atomic::{AtomicBool, Ordering as AtomicOrdering},
};
use prime_factorization::Factorization;
use radixal::IntoDigits;
use thiserror::Error;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Arg
{
    Integer { sign: bool, val: u128 },
    Fraction { sign: bool, num: u128, denom: u128 },
    Decimal { sign: bool, mantissa: u128, exp: u8 },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct Fraction { sign: bool, num: u128, denom: u128 }

fn main()
{
    for arg in parse_args()
    {
        print!("{arg} = ");
        io::stdout().flush().expect("failed to flush stdout");

        let frac = arg.into();
        match frac
        {
            Fraction { num: 0, denom: 0, .. } => { println!("0/0"); continue },
            Fraction { num: 0, .. } => { println!("0"); continue },
            Fraction { sign: false, num, denom } if num == denom => { println!("1"); continue },
            Fraction { sign: true, num, denom } if num == denom => { println!("-1"); continue },
            _ => (),
        }

        let mut first = true;
        if frac.sign { print!("-1"); first = false; }

        let mut reduced = Fraction { sign: frac.sign, num: 1, denom: 1 };
        let mut print_reduced = false;

        for (val, exp) in factorize(frac.num, frac.denom)
        {
            if exp > 0 { reduced.num *= num::pow(val, exp as usize) }
            else { reduced.denom *= num::pow(val, exp.abs() as usize) }

            if first
            {
                if exp == 1 { print!("{val}") }
                else { print!("{val}^{exp}"); print_reduced = true }
            }
            else
            {
                if exp == 1 { print!(" * {val}") }
                else { print!(" * {val}^{exp}") }

                print_reduced = true;
            }

            first = false;
        }

        if frac.denom == 0
        {
            if first { print!("1/0") } else { print!(" * 1/0") }
        }
        else
        {
            if first { panic!("no factors") }

            print_reduced &= match arg
            {
                Arg::Integer { .. } => false,
                Arg::Fraction { .. } if frac != reduced => true,
                Arg::Fraction { .. } => false,
                Arg::Decimal { .. } => true,
            };

            if print_reduced { print!(" = {reduced}") }
        }

        println!();
    }
}

fn factorize(numerator: u128, denominator: u128) -> impl Iterator<Item = (u128, i64)>
{
    let mut num = Factorization::run(numerator)
        .prime_factor_repr()
        .into_iter()
        .map(|(val, exp)| (val, exp as i64));

    let mut denom = Factorization::run(denominator)
        .prime_factor_repr()
        .into_iter()
        .map(|(val, exp)| (val, -(exp as i64)));

    let mut num_curr = num.next();
    let mut denom_curr = denom.next();

    iter::from_fn(move ||
    {
        let Some((num_val, num_exp)) = num_curr else
        {
            let res = denom_curr;
            denom_curr = denom.next();
            return res
        };

        let Some((denom_val, denom_exp)) = denom_curr else
        {
            let res = num_curr;
            num_curr = num.next();
            return res
        };

        match num_val.cmp(&denom_val)
        {
            Ordering::Less =>
            {
                num_curr = num.next();
                Some((num_val, num_exp))
            },
            Ordering::Equal =>
            {
                num_curr = num.next();
                denom_curr = denom.next();
                Some((num_val, num_exp + denom_exp))
            },
            Ordering::Greater =>
            {
                denom_curr = denom.next();
                Some((denom_val, denom_exp))
            },
        }
    })
    .filter(|(val, exp)| *exp != 0 && *val != 1 && *val != 0)
}

fn parse_args() -> Vec<Arg>
{
    let print_try_help = AtomicBool::new(false);
    let mut print_help = false;
    let mut print_version = false;
    let mut seen_double_dash = false;

    let res = env::args_os()
        .enumerate()
        .skip(1)
        .filter_map(|(i, s)| s
            .into_string()
            .map_err(|_|
            {
                eprintln!("error: argument {i} is not valid unicode");
                print_try_help.store(true, AtomicOrdering::Relaxed);
            })
            .ok()
        )
        .filter(|s| seen_double_dash || match s.trim().strip_prefix("--")
        {
            Some("help") => { print_help = true; false },
            Some("version") => { print_version = true; false },
            Some("") => { seen_double_dash = true; false },
            Some(opt) =>
            {
                eprintln!("error: unknown option '{opt}'");
                print_try_help.store(true, AtomicOrdering::Relaxed);
                false
            },
            None => true,
        })
        .filter_map(|s| s
            .parse()
            .map_err(|e|
            {
                eprintln!("error: argument '{s}' is not a valid number: {e}");
                print_try_help.store(true, AtomicOrdering::Relaxed);
            })
            .ok()
        )
        .collect();

    if print_version { eprintln!("{} v{}", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION")) }

    if print_help
    {
        eprintln!("{}: {}", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_DESCRIPTION"));
        eprintln!("usage: {} [NUMBERS]...",
        {
            #[cfg(windows)] { concat!(env!("CARGO_BIN_NAME"), ".exe") }
            #[cfg(not(windows))] { env!("CARGO_BIN_NAME") }
        });
        eprintln!("options:");
        eprintln!("  --help     Print help");
        eprintln!("  --version  Print version");
    }
    else if print_try_help.into_inner() { eprintln!("for more information, try '--help'") }

    res
}

impl str::FromStr for Arg
{
    type Err = ArgError;
    fn from_str(s: &str) -> Result<Arg, ArgError> { Arg::try_from(s) }
}

impl TryFrom<&str> for Arg
{
    type Error = ArgError;

    fn try_from(s: &str) -> Result<Arg, ArgError>
    {
        fn pair<T>(mut iter: impl Iterator<Item = T>) -> Result<(T, T), usize>
        {
            let Some(first) = iter.next() else { return Err(0) };
            let Some(second) = iter.next() else { return Err(1) };

            let rest = iter.count();
            if rest != 0 { return Err(2 + rest); }

            Ok((first, second))
        }

        fn parse_signed(s: &str) -> Result<(bool, u128), ParseIntError>
        {
            let mut sign = false;

            let s = if let Some(val) = s.strip_prefix('-') { sign = true; val } else { s };
            Ok((sign, s.parse()?))
        }

        match pair(s.split('/'))
        {
            Ok((num, denom)) => match pair(s.split('.'))
            {
                Ok(_) => Err(ArgError::DecimalInFraction),
                Err(0 | 1) =>
                {
                    let (num_sign, num) = parse_signed(num.trim())
                        .map_err(ArgError::NumeratorInvalid)?;

                    let (mut denom_sign, denom) = parse_signed(denom.trim())
                        .map_err(ArgError::DenominatorInvalid)?;

                    if denom == 0 { denom_sign = false }

                    Ok(Arg::Fraction { sign: num_sign ^ denom_sign, num, denom })
                },
                Err(n) => Err(ArgError::TooManyDecimals(n - 1)),
            },
            Err(0 | 1) => match pair(s.split('.'))
            {
                Ok((whole, decimal)) =>
                {
                    let (sign, whole) = match whole.trim_start()
                    {
                        "" => (false, 0),
                        "-" => (true, 0),
                        s => parse_signed(s).map_err(ArgError::DecimalInvalid)?,
                    };

                    let decimal = decimal.trim_end().trim_end_matches('0');
                    let exp = decimal.len();
                    let decimal = if decimal.is_empty() { 0 }
                    else { decimal.parse().map_err(ArgError::DecimalInvalid)? };

                    if exp > 38 { return Err(ArgError::DecimalExpTooLarge(exp)) }
                    let mantissa = whole
                        .checked_mul(num::pow(10, exp))
                        .and_then(|n| n.checked_add(decimal))
                        .ok_or(ArgError::MantissaTooLarge)?;

                    if exp == 0 { Ok(Arg::Integer { sign, val: mantissa }) }
                    else { Ok(Arg::Decimal { sign, mantissa, exp: exp as u8 }) }
                },
                Err(0 | 1) =>
                {
                    let (sign, val) = parse_signed(s.trim())
                        .map_err(ArgError::IntegerInvalid)?;

                    Ok(Arg::Integer { sign, val })
                },
                Err(n) => Err(ArgError::TooManyDecimals(n - 1)),
            },
            Err(n) => Err(ArgError::TooManyFractions(n - 1)),
        }
    }
}

#[derive(Error, Debug, Clone)]
enum ArgError
{
    #[error("cannot contain multiple fraction separators (expected 1, found {0})")]
    TooManyFractions(usize),
    #[error("cannot contain multiple decimal points (expected 1, found {0})")]
    TooManyDecimals(usize),
    #[error("decimal numbers are not allowed in fractions")]
    DecimalInFraction,
    #[error("decimal numbers cannot have more than 38 digits (found {0})")]
    DecimalExpTooLarge(usize),
    #[error("decimal number mantissa too large to fit in target type")]
    MantissaTooLarge,
    #[error("numerator invalid: {0}")]
    NumeratorInvalid(ParseIntError),
    #[error("denominator invalid: {0}")]
    DenominatorInvalid(ParseIntError),
    #[error("decimal number invalid: {0}")]
    DecimalInvalid(ParseIntError),
    #[error("integer invalid: {0}")]
    IntegerInvalid(ParseIntError),
}

impl From<Arg> for Fraction
{
    fn from(arg: Arg) -> Fraction
    {
        match arg
        {
            Arg::Integer { sign, val } => Fraction { sign, num: val, denom: 1 },
            Arg::Fraction { sign, num, denom } => Fraction { sign, num, denom },
            Arg::Decimal { sign, mantissa, exp } => Fraction
            {
                sign,
                num: mantissa,
                denom: num::pow(10, exp as usize),
            },
        }
    }
}

impl fmt::Display for Arg
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result
    {
        match self
        {
            Arg::Integer { val: 0, .. } => write!(f, "0"),
            Arg::Integer { sign: false, val } => write!(f, "{val}"),
            Arg::Integer { sign: true, val } => write!(f, "-{val}"),
            Arg::Fraction { num: 0, denom, .. } => write!(f, "0/{denom}"),
            Arg::Fraction { sign: false, num, denom } => write!(f, "{num}/{denom}"),
            Arg::Fraction { sign: true, num, denom } => write!(f, "-{num}/{denom}"),
            Arg::Decimal { sign, mantissa, exp } =>
            {
                let mut digits = mantissa
                    .into_decimal_digits()
                    .rev()
                    .enumerate()
                    .rev()
                    .map(|(i, d)|
                        (i as u8, char::from_digit(d as u32, 10).expect("invalid digit"))
                    );

                let Some((i, digit)) = digits.next() else { return write!(f, "0.0") };
                if *sign { write!(f, "-")? }

                if i < *exp
                {
                    write!(f, "0.")?;
                    for _ in 0..(exp - i - 1) { write!(f, "0")? }
                }

                write!(f, "{digit}")?;
                let mut trailing_zero = if i == *exp { write!(f, ".")?; true } else { false };

                for (i, digit) in digits
                {
                    write!(f, "{digit}")?;
                    trailing_zero = if i == *exp { write!(f, ".")?; true } else { false };
                }

                if trailing_zero { write!(f, "0") } else { Ok(()) }
            },
        }
    }
}

impl fmt::Display for Fraction
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result
    {
        match self
        {
            Fraction { num: 0, denom: 0, .. } => write!(f, "0/0"),
            Fraction { num: 0, .. } => write!(f, "0"),
            Fraction { denom: 0, .. } => write!(f, "1/0"),
            Fraction { sign: false, num, denom: 1 } => write!(f, "{num}"),
            Fraction { sign: true, num, denom: 1 } => write!(f, "-{num}"),
            Fraction { sign: false, num, denom } => write!(f, "{num}/{denom}"),
            Fraction { sign: true, num, denom } => write!(f, "-{num}/{denom}"),
        }
    }
}
