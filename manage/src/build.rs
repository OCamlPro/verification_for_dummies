fn main() {
    match run() {
        Ok(()) => (),
        Err(e) => panic!("error: {}", e),
    }
}

fn run() -> Result<(), String> {
    let res = check_z3_cmd();
    if res.is_err() {
        println!("There seems to be a problem with Z3:");
        println!("- a relatively recent version of Z3 must be in you path,");
        println!("  available here: https://github.com/Z3Prover/z3/releases;");
        println!("- Z3's binary must be named `{}`.", Z3_CMD);
        println!(
            "Run `{} {}` in a terminal to make sure these conditions are met.",
            Z3_CMD, Z3_VERSION_ARG
        );
    }
    res?;

    Ok(())
}

const Z3_CMD: &str = "z3";
const Z3_VERSION_ARG: &str = "-version";

fn check_z3_cmd() -> Result<(), String> {
    use std::{
        io::ErrorKind as EKind,
        process::{Command, Stdio},
    };

    let status = Command::new(Z3_CMD)
        .arg(Z3_VERSION_ARG)
        .stderr(Stdio::null())
        .stdout(Stdio::null())
        .stdin(Stdio::null())
        .status();
    match status {
        Ok(status) => {
            if status.success() {
                println!("default z3 command is live");
                Ok(())
            } else {
                Err(format!(
                    "`{} {}` returned with status {}",
                    Z3_CMD,
                    Z3_VERSION_ARG,
                    status
                        .code()
                        .map(|c| c.to_string())
                        .unwrap_or_else(|| format!("??")),
                ))
            }
        }
        Err(e) => {
            if e.kind() == EKind::NotFound {
                Err(format!("default z3 command `{}` not found in path", Z3_CMD))
            } else {
                Err(format!(
                    "`{} {}` yielded an error: {}",
                    Z3_CMD, Z3_VERSION_ARG, e,
                ))
            }
        }
    }
}
