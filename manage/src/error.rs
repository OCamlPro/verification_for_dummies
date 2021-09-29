//! Error-handling.

error_chain::error_chain! {
    types {
        Error, ErrorKind, ResExt, Res;
    }

    foreign_links {
        Io(std::io::Error);
    }
}

impl Error {
    /// Pretty-prints the error(s) on `stderr`.
    pub fn pretty_eprint(&self, pref: &str) {
        const PREF_0: &str = "- ";
        const PREF_N: &str = "  ";
        for e in self.iter() {
            let s = e.to_string();
            for (idx, line) in s.lines().enumerate() {
                if idx == 0 {
                    eprint!("{}{}", pref, PREF_0)
                } else {
                    eprint!("{}{}", pref, PREF_N)
                }
                eprintln!("{}", line);
            }
        }
    }
}
