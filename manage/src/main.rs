//! Book manager.

manage_api::prelude!();

const VERB_KEY: &str = "VERB";
const CHECK_SMT2_KEY: &str = "CHECK_SMT2";
const CHECK_MIKINO_KEY: &str = "CHECK_MIKINO";
const Z3_CMD_KEY: &str = "Z3_CMD";
const MIKINO_CMD_KEY: &str = "MIKINO_CMD";
const VANILLA_MODE: &str = "vanilla";
const VANILLA_TARGET_KEY: &str = "vanilla";

fn main() {
    let matches = {
        use clap::{App, Arg, SubCommand};
        App::new("manager")
            .args(&[
                Arg::with_name(VERB_KEY)
                    .short("v")
                    .help("Increases verbosity (max 2)")
                    .multiple(true),
                Arg::with_name(CHECK_SMT2_KEY)
                    .long("check_smt2")
                    .help("(De)activates checks for `.smt2` files")
                    .takes_value(true)
                    .validator(|s| check_bool_arg(&s))
                    .default_value("on"),
                Arg::with_name(Z3_CMD_KEY)
                    .long("z3_cmd")
                    .help("Command to run Z3 to check `.stm2` files")
                    .takes_value(true)
                    .default_value("z3"),
                Arg::with_name(CHECK_MIKINO_KEY)
                    .long("check_mikino")
                    .help("(De)activates checks for `.mkn` files")
                    .takes_value(true)
                    .validator(|s| check_bool_arg(&s))
                    .default_value("on"),
                Arg::with_name(MIKINO_CMD_KEY)
                    .long("mikino_cmd")
                    .help("Command to run mikino to check `.mkn` files")
                    .takes_value(true)
                    .default_value("mikino"),
            ])
            .subcommand(
                SubCommand::with_name(VANILLA_MODE)
                    .about("generates vanilla markdown, inlines all code blocks")
                    .arg(
                        Arg::with_name(VANILLA_TARGET_KEY)
                            .long("target")
                            .help("Output directory for vanilla markdown")
                            .takes_value(true)
                            .default_value("target/vanilla"),
                    ),
            )
            .get_matches()
    };
    let log_level = match matches.occurrences_of(VERB_KEY) {
        0 => log::LevelFilter::Info,
        1 => log::LevelFilter::Debug,
        _ => log::LevelFilter::Trace,
    };

    simple_logger::SimpleLogger::new()
        .with_level(log_level)
        .init()
        .expect("failed to initialize logger");

    match run(&matches) {
        Ok(()) => std::process::exit(0),
        Err(e) => {
            eprintln!("|===| Error(s):");
            e.pretty_eprint("| ");
            eprintln!("|===|");
            std::process::exit(2);
        }
    }
}

fn run(matches: &clap::ArgMatches) -> Res<()> {
    let test_smt2 = bool_arg(
        matches
            .value_of(CHECK_SMT2_KEY)
            .expect("argument with default value"),
    )
    .expect("already checked by validator");
    let z3_cmd = matches
        .value_of(Z3_CMD_KEY)
        .expect("argument with default value");
    let test_mikino = bool_arg(
        matches
            .value_of(CHECK_MIKINO_KEY)
            .expect("argument with default value"),
    )
    .expect("already checked by validator");
    let mikino_cmd = matches
        .value_of(MIKINO_CMD_KEY)
        .expect("argument with default value");

    let conf = Conf::new()
        .set_smt2(test_smt2, z3_cmd)
        .set_mikino(test_mikino, mikino_cmd);

    if let Some(matches) = matches.subcommand_matches(VANILLA_MODE) {
        let target = matches
            .value_of(VANILLA_TARGET_KEY)
            .expect("argument with default value");
        let vanilla = Vanilla::new(conf, target);
        log::info!("generating vanilla markdown to `{}`", vanilla.target());

        vanilla.run()?;
    } else {
        conf.check(".")?;
    }

    Ok(())
}

fn check_bool_arg(arg: &str) -> Result<(), String> {
    bool_arg(arg).map(|_| ())
}
fn bool_arg(arg: &str) -> Result<bool, String> {
    match arg {
        "on" | "true" => Ok(true),
        "off" | "false" => Ok(false),
        _ => Err(format!(
            "unexpected boolean value `{}`, expected `on|true|off|false`",
            arg
        )),
    }
}
