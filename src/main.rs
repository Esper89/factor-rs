use std::{
    env,
    fmt,
    io::{self, Write as _},
    num::ParseIntError,
    str,
    sync::atomic::{AtomicBool, Ordering as AtomicOrdering},
};
use radixal::IntoDigits;
use thiserror::Error;
use factor_rs::Fraction;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Arg
{
    Integer { sign: bool, val: u128 },
    Fraction { sign: bool, num: u128, denom: u128 },
    Decimal { sign: bool, mantissa: u128, exp: u8 },
}

fn main()
{
    for arg in parse_args()
    {
        print!("{arg} = ");
        io::stdout().flush().expect("failed to flush stdout");

        let frac: Fraction = arg.into();
        let mut factors = frac.factorize();

        let mut reduced = Fraction::ONE;
        let mut print_reduced = false;

        if let Some(fact) = factors.next()
        {
            print!("{fact}");

            reduced *= Into::<Fraction>::into(fact);
            if fact.has_exponent() { print_reduced = true }

            for fact in factors
            {
                print!(" * {fact}");

                reduced *= Into::<Fraction>::into(fact);
                print_reduced = true;
            }
        }

        if print_reduced
            && matches!(arg, Arg::Fraction { .. } | Arg::Decimal { .. })
            && frac != reduced
        {
            print!(" = {reduced}");
        }

        println!();
    }
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

        match pair(s.split('/'))
        {
            Ok((num, denom)) => match pair(s.split('.'))
            {
                Ok(_) => Err(ArgError::DecimalInFraction),
                Err(0 | 1) => parse_frac(num, denom),
                Err(n) => Err(ArgError::TooManyDecimals(n - 1)),
            },
            Err(0 | 1) => match pair(s.split('.'))
            {
                Ok((whole, decimal)) => parse_decimal(whole, decimal),
                Err(0 | 1) => parse_int(s),
                Err(n) => Err(ArgError::TooManyDecimals(n - 1)),
            },
            Err(n) => Err(ArgError::TooManyFractions(n - 1)),
        }
    }
}

fn parse_int(val: &str) -> Result<Arg, ArgError>
{
    let (sign, val) = parse_signed(val.trim()).map_err(ArgError::IntegerInvalid)?;

    Ok(Arg::Integer { sign, val })
}

fn parse_frac(num: &str, denom: &str) -> Result<Arg, ArgError>
{
    let (mut num_sign, num) = parse_signed(num.trim()).map_err(ArgError::NumeratorInvalid)?;
    let (mut denom_sign, denom) = parse_signed(denom.trim()).map_err(ArgError::DenominatorInvalid)?;

    if num == 0 { num_sign = false }
    if denom == 0 { denom_sign = false }

    Ok(Arg::Fraction { sign: num_sign ^ denom_sign, num, denom })
}

fn parse_decimal(whole: &str, decimal: &str) -> Result<Arg, ArgError>
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
}

fn parse_signed(s: &str) -> Result<(bool, u128), ParseIntError>
{
    let mut sign = false;

    let s = if let Some(val) = s.strip_prefix('-') { sign = true; val } else { s };
    Ok((sign, s.parse()?))
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
            Arg::Fraction { num: 0, denom: 0, .. } => write!(f, "0/0"),
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
