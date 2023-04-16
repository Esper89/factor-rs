use std::io::{self, Write as _};
use prime_factorization::Factorization;

fn main()
{
    let numbers = parse_args();

    for num in numbers
    {
        print!("{num} = ");
        io::stdout().flush().expect("failed to flush stdout");

        let mut factors = Factorization::run(num).prime_factor_repr().into_iter();

        if let Some((val, exp)) = factors.next()
        {
            if exp == 1 { print!("{val}") }
            else { print!("{val}^{exp}") }

            for (val, exp) in factors
            {
                if exp == 1 { print!(" * {val}") }
                else { print!(" * {val}^{exp}") }
            }
        }
        else { print!("{num}") }

        println!();
        io::stdout().flush().expect("failed to flush stdout");
    }
}

#[cfg(feature = "full-cli")]
fn parse_args() -> Vec<u128>
{
    #[derive(clap::Parser)]
    #[command(version, about)]
    struct Args { numbers: Vec<u128> }

    <Args as clap::Parser>::parse().numbers
}

#[cfg(not(feature = "full-cli"))]
fn parse_args() -> Vec<u128>
{
    std::env::args_os()
        .enumerate()
        .skip(1)
        .filter_map(|(i, s)| s
            .into_string()
            .map_err(|_| eprintln!("argument {i} is not a valid integer: invalid unicode"))
            .ok()
        )
        .filter_map(|s| s
            .trim()
            .parse()
            .map_err(|e| eprintln!("argument '{s}' is not a valid integer: {e}"))
            .ok()
        )
        .collect()
}
