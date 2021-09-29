//! Book manager.

mod error;

#[macro_export]
macro_rules! prelude {
    {} => { use $crate::prelude::*; }
}

/// Crate's prelude.
pub mod prelude {
    pub use std::{
        fs, io,
        path::{Path, PathBuf},
    };

    pub use error_chain::bail;
    pub use log;

    pub use crate::{
        prelude::err::{Res, ResExt},
        test, Conf, Vanilla,
    };

    pub mod err {
        pub use crate::error::*;
    }

    /// Loads the content of a file.
    pub fn load_file(path: impl AsRef<Path>) -> Res<String> {
        use std::{
            fs::OpenOptions,
            io::{BufReader, Read},
        };
        let path = path.as_ref();

        let reader = OpenOptions::new()
            .read(true)
            .open(path)
            .chain_err(|| format!("while read-opening file `{}`", path.display()))?;
        let mut reader = BufReader::new(reader);
        let mut content = String::new();
        reader
            .read_to_string(&mut content)
            .chain_err(|| format!("while reading file `{}`", path.display()))?;
        Ok(content)
    }

    /// Opens a writer on a file.
    pub fn open_write(path: impl AsRef<Path>) -> Res<fs::File> {
        use std::fs::OpenOptions;
        let path = path.as_ref();

        let file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(path)
            .chain_err(|| format!("while write-opening file `{}`", path.display()))?;
        Ok(file)
    }
}

prelude!();

/// Test configuration.
#[derive(Clone, Debug)]
pub struct Conf<'s> {
    check_smt2: Option<(bool, &'s str)>,
    check_mikino: Option<(bool, &'s str)>,
}
impl Default for Conf<'static> {
    fn default() -> Self {
        Self {
            check_smt2: Some((true, "z3")),
            check_mikino: Some((true, "mikino")),
        }
    }
}
impl<'s> Conf<'s> {
    /// Constructor.
    pub fn new() -> Self {
        Self {
            check_smt2: None,
            check_mikino: None,
        }
    }

    pub fn set_smt2(mut self, check: bool, command: &'s str) -> Self {
        self.check_smt2 = Some((check, command));
        self
    }
    pub fn set_mikino(mut self, check: bool, command: &'s str) -> Self {
        self.check_mikino = Some((check, command));
        self
    }

    fn get_smt2(&self) -> Res<(bool, &'s str)> {
        self.check_smt2.ok_or_else(|| {
            format!("[internal] no information provided for SMT file checking").into()
        })
    }
    fn get_mikino(&self) -> Res<(bool, &'s str)> {
        self.check_mikino.ok_or_else(|| {
            format!("[internal] no information provided for mikino file checking").into()
        })
    }

    /// Runs the actual checks.
    pub fn check(&self, path: impl AsRef<Path>) -> Res<()> {
        test::run(self, path)
    }
}

/// Test functions.
pub mod test {
    use std::io::Read;

    prelude!();

    #[test]
    fn test_all() -> () {
        simple_logger::SimpleLogger::new()
            .with_level(log::LevelFilter::Trace)
            .init()
            .expect("failed to initialize logger");
        let out = std::process::Command::new("pwd").output().unwrap();
        println!("pwd: {}", String::from_utf8_lossy(&out.stdout));
        let conf = Conf::default();
        match run(&conf, "..") {
            Ok(()) => (),
            Err(e) => {
                eprintln!("|===| Error(s):");
                e.pretty_eprint("| ");
                eprintln!("|===|");
                panic!("test failed")
            }
        }
    }

    /// Runs all the tests.
    pub fn run(conf: &Conf, path: impl AsRef<Path>) -> Res<()> {
        let path = path.as_ref();

        log::info!("testing book...");
        test::book(path)?;

        log::info!("testing code snippets");
        let mut src_path = path.to_path_buf();
        src_path.push("src");
        test::code_out(conf, src_path)?;

        log::info!("everything okay");
        Ok(())
    }

    /// Tests the book itself.
    pub fn book(path: impl AsRef<Path>) -> Res<()> {
        use std::process::Command;

        log::info!("building with `mdbook`");
        let status = Command::new("mdbook")
            .arg("build")
            .arg("--")
            .arg(path.as_ref())
            .status()
            .chain_err(|| "failed to run `mdbook test`")?;
        if !status.success() {
            bail!("`mdbook build` returned with an error")
        }

        log::info!("testing with `mdbook`");
        let status = Command::new("mdbook")
            .arg("test")
            .arg("--")
            .arg(path.as_ref())
            .status()
            .chain_err(|| "failed to run `mdbook test`")?;
        if !status.success() {
            bail!("`mdbook test` returned with an error")
        }
        Ok(())
    }

    macro_rules! dir_read_err {
        { $dir:expr } => {
            || format!("while reading directory `{}`", $dir)
        };
    }

    /// Tests the code snippets that have a `.out` file.
    pub fn code_out(conf: &Conf, path: impl AsRef<Path>) -> Res<()> {
        code_out_in(conf, path)
    }
    /// Searches for `code` directories in `src`, recursively.
    fn code_out_in(conf: &Conf, src: impl AsRef<Path>) -> Res<()> {
        const CODE_DIR: &str = "code";
        let src = src.as_ref().to_path_buf();
        log::trace!("code_out_in({})", src.display());

        if !(src.exists() && src.is_dir()) {
            bail!("expected directory path, got `{}`", src.display())
        }

        'sub_dirs: for entry_res in src.read_dir().chain_err(dir_read_err!(src.display()))? {
            let entry = entry_res.chain_err(dir_read_err!(src.display()))?;
            let entry_path = entry.path();
            if !entry_path.is_dir() {
                continue 'sub_dirs;
            }

            log::trace!("code_out_in: looking at `{}`", entry_path.display());

            // `code` directory, check what's inside
            if entry_path
                .file_name()
                .map(|name| name == CODE_DIR)
                .unwrap_or(false)
            {
                code_out_check(conf, &entry_path).chain_err(|| {
                    format!("while checking code snippets in `{}`", entry_path.display())
                })?
            }

            // just a sub-directory, go down
            code_out_in(conf, entry_path)?
        }

        Ok(())
    }
    /// Tests a `code` directory at `path`.
    ///
    /// Scans the files in `path`, looking for *output* files with a `<name>.out` extension. Such
    /// files must have an associated file `<name>`. The output file contains the output of
    /// whatever tool corresponds to file `<name>`'s extension.
    ///
    /// For instance, `<name>.smt2` file's corresponding tool is Z3 and the output file contains
    /// the output of `z3 <name>.smt2`.
    fn code_out_check(conf: &Conf, path: impl AsRef<Path>) -> Res<()> {
        const OUT_SUFF: &str = "out";
        let path = path.as_ref();
        log::trace!("code_out_check({})", path.display());

        'out_files: for entry_res in path.read_dir().chain_err(dir_read_err!(path.display()))? {
            let entry = entry_res.chain_err(dir_read_err!(path.display()))?;
            let entry_path = entry.path();
            if entry_path.is_dir() {
                continue 'out_files;
            }
            log::trace!("working on `{}`", entry_path.display());

            let is_out_file = entry_path
                .extension()
                .map(|ext| {
                    log::trace!("ext: `{}`", ext.to_string_lossy());
                    ext == OUT_SUFF
                })
                .unwrap_or(false);

            if !is_out_file {
                log::trace!("not an `out` file");
                warn_if_not_tested(path, entry_path)?;
                continue 'out_files;
            }

            let out_path = entry_path;
            let snippet_path = {
                let mut path = out_path.clone();
                let stem = path
                    .file_stem()
                    .ok_or_else(|| {
                        format!("could not retrieve file stem for `{}`", path.display())
                    })?
                    .to_owned();
                let okay = path.pop();
                if !okay {
                    bail!("problem popping last part of path `{}`", path.display());
                }
                path.push(stem);
                path
            };

            log::trace!(
                "out: {}, snippet: {}",
                out_path.display(),
                snippet_path.display()
            );

            let ext = snippet_path
                .extension()
                .ok_or_else(|| {
                    format!(
                        "could not retrieve extension for `{}`",
                        snippet_path.display()
                    )
                })?
                .to_string_lossy();

            let err = || {
                format!(
                    "while checking `{}` with out file `{}`",
                    snippet_path.display(),
                    out_path.display()
                )
            };

            let actually_okay = if ext == "smt2" {
                code_out_check_smt2(conf, &out_path, &snippet_path).chain_err(err)?
            } else if ext == "mkn" {
                code_out_check_mkn(conf, &out_path, &snippet_path).chain_err(err)?
            } else if ext == "rs" {
                code_out_check_rs(conf, &out_path, &snippet_path).chain_err(err)?
            } else {
                bail!(
                    "unknown extension `{}` for code snippet `{}` with out file `{}`",
                    ext,
                    snippet_path.display(),
                    out_path.display()
                )
            };

            if actually_okay {
                log::debug!(
                    "`{}` is okay w.r.t. `{}`",
                    snippet_path.display(),
                    out_path.display()
                );
            }
        }

        Ok(())
    }

    /// Checks a non-output file, issues a warning if there is a problem.
    ///
    /// A non-output file `name.ext` must be such that either
    ///
    /// - `ext` is `rs`: Rust files are checked by `mdbook` itself, or
    /// - there exists a `name.ext.out` file, which will be handled by regular testing.
    ///
    /// Otherwise we have non-Rust file with no output file, meaning the file is not tested against
    /// anything. We assume the author forgot the output file and issue a warning.
    fn warn_if_not_tested(parent: impl AsRef<Path>, snippet_path: impl AsRef<Path>) -> Res<()> {
        let (parent, snippet) = (parent.as_ref(), snippet_path.as_ref());

        // Rust files are tested by `mdbook`, no need for output file.
        if snippet.extension().map(|ext| ext == "rs").unwrap_or(false) {
            return Ok(());
        }

        // Not a Rust file, construct expected output file path and check it exists.
        let file_name = snippet
            .file_name()
            .ok_or_else(|| format!("failed to retrieve filename from `{}`", snippet.display()))?;
        let out_file = {
            let mut parent = parent.to_path_buf();
            parent.push(format!("{}.out", file_name.to_string_lossy()));
            parent
        };
        if !out_file.exists() {
            log::warn!(
                "file `{}` has no output file, no way to test it",
                snippet.display()
            );
        }
        if out_file.is_dir() {
            log::warn!(
                "file `{}` has no output 'file', `{}` exists but is a directory",
                snippet.display(),
                out_file.display()
            );
        }

        Ok(())
    }

    /// Compares the output of a command to the content of a file.
    fn cmd_output_same_as_file_content(
        cmd: &mut std::process::Command,
        path: impl AsRef<Path>,
    ) -> Res<()> {
        let path = path.as_ref();
        let output = cmd
            .output()
            .chain_err(|| format!("running command {:?}", cmd))?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let expected = {
            use std::{fs::OpenOptions, io::BufReader};
            let mut file = BufReader::new(
                OpenOptions::new()
                    .read(true)
                    .open(path)
                    .chain_err(|| format!("while read-opening `{}`", path.display()))?,
            );
            let mut buf = String::new();
            file.read_to_string(&mut buf)
                .chain_err(|| format!("while reading `{}`", path.display()))?;
            buf
        };
        if stdout != expected {
            bail!("unexpected output for `{:?}`", cmd)
        } else {
            Ok(())
        }
    }

    /// Checks a single `.smt2` file `snippet_path` against its output file `out_path`.
    fn code_out_check_smt2(
        conf: &Conf,
        out_path: impl AsRef<Path>,
        snippet_path: impl AsRef<Path>,
    ) -> Res<bool> {
        let (out_path, snippet_path) = (out_path.as_ref(), snippet_path.as_ref());
        let (check_smt2, z3_cmd) = conf.get_smt2()?;
        if !check_smt2 {
            log::warn!(
                "SMT2 checking deactivated, skipping `{}` (`{}`)",
                snippet_path.display(),
                out_path.display()
            );
            return Ok(false);
        }
        let mut cmd = std::process::Command::new(z3_cmd);
        cmd.arg("-T:5").arg(snippet_path);
        let () = cmd_output_same_as_file_content(&mut cmd, out_path)?;

        Ok(true)
    }

    /// Checks a single `.mkn` file `snippet_path` against its output file `out_path`.
    fn code_out_check_mkn(
        conf: &Conf,
        out_path: impl AsRef<Path>,
        snippet_path: impl AsRef<Path>,
    ) -> Res<bool> {
        let (out_path, snippet_path) = (out_path.as_ref(), snippet_path.as_ref());
        let (check_mikino, mikino_cmd) = conf.get_mikino()?;
        if !check_mikino {
            log::warn!(
                "mikino checking deactivated, skipping `{}` (`{}`)",
                snippet_path.display(),
                out_path.display()
            );
            return Ok(false);
        }

        let (_, z3_cmd) = conf.get_smt2()?;
        let mut cmd = retrieve_mkn_cmd(mikino_cmd, z3_cmd, snippet_path, "//")?;
        cmd_output_same_as_file_content(&mut cmd, out_path)?;

        Ok(true)
    }

    fn retrieve_mkn_cmd(
        mikino_cmd: &str,
        z3_cmd: &str,
        path: impl AsRef<Path>,
        pref: &str,
    ) -> Res<std::process::Command> {
        let path = path.as_ref();
        // Mikino files are expected to start with a special line specifying the command to run.
        let cmd_line = first_line_of(path)?
            .ok_or_else(|| "first line of `mkn` files must specify a `mikino` command")?;
        const CMD_PREF: &str = " CMD: ";
        if !cmd_line.starts_with(pref) || !cmd_line[pref.len()..].starts_with(CMD_PREF) {
            bail!(
                "first line of `mkn` files should start with `{}{}` to specify the mikino command",
                pref,
                CMD_PREF,
            )
        }

        let start = pref.len() + CMD_PREF.len();
        let cmd_line = &cmd_line[start..];
        let mut elems = cmd_line.split_whitespace();

        match elems.next() {
            Some("mikino") => (),
            Some(tkn) => bail!(
                "unexpected token `{}` on first line, expected `mikino`",
                tkn,
            ),
            None => bail!("expected `mikino` command on first line"),
        }

        let mut cmd = std::process::Command::new(mikino_cmd);
        cmd.arg("--z3_cmd").arg(&format!("{} -T:5", z3_cmd));

        for arg in elems {
            if arg == "<file>" {
                cmd.arg(path);
            } else {
                cmd.arg(arg);
            }
        }

        Ok(cmd)
    }

    /// Checks a single `.mkn` file `snippet_path` against its output file `out_path`.
    fn code_out_check_rs(
        _conf: &Conf,
        out_path: impl AsRef<Path>,
        snippet_path: impl AsRef<Path>,
    ) -> Res<bool> {
        let (out_path, snippet_path) = (out_path.as_ref(), snippet_path.as_ref());

        let tmpfile = PathBuf::from("./dont_exist_please_CI_does_not_like_tempfile");
        let mut cmd = std::process::Command::new("rustc");
        cmd.arg("-o").arg(&tmpfile).arg(snippet_path);
        let cmd_string = || format!("rustc -o {} {}", tmpfile.display(), snippet_path.display());
        let status = cmd
            .status()
            .chain_err(|| format!("while running {}", cmd_string()))?;
        if !status.success() {
            bail!(
                "command `{}` was not successful, exit code {}",
                cmd_string(),
                status
                    .code()
                    .map(|i| i.to_string())
                    .unwrap_or_else(|| "??".into())
            )
        }
        let mut cmd = std::process::Command::new(&tmpfile);
        cmd_output_same_as_file_content(&mut cmd, out_path)?;

        // Delete temporary file.
        std::fs::remove_file(&tmpfile)
            .chain_err(|| format!("while deleting temp file `{}`", tmpfile.display()))?;

        Ok(true)
    }

    /// Retrieves the first line of a file.
    ///
    /// Some code snippets are expected to specify, on their first line, the command used to run
    /// them. Mikino files, for example.
    fn first_line_of(path: impl AsRef<Path>) -> Res<Option<String>> {
        use std::{
            fs::OpenOptions,
            io::{BufRead, BufReader},
        };

        let path = path.as_ref();
        let mut reader = BufReader::new(
            OpenOptions::new()
                .read(true)
                .open(path)
                .chain_err(|| format!("while read-opening file `{}`", path.display()))?,
        );

        let mut line = String::with_capacity(31);
        let bytes_read = reader
            .read_line(&mut line)
            .chain_err(|| format!("while reading for line of file `{}`", path.display()))?;

        if bytes_read == 0 {
            Ok(None)
        } else {
            line.shrink_to_fit();
            Ok(Some(line))
        }
    }
}

/// A top-level markdown file, a path and a name.
pub struct TopLevelMd {
    path: String,
    title: String,
}

/// Vanilla markdown generator.
pub struct Vanilla<'s> {
    target: &'s str,
    #[allow(dead_code)]
    conf: Conf<'s>,
}
impl<'s> Vanilla<'s> {
    /// Constructor.
    pub fn new(conf: Conf<'s>, target: &'s str) -> Self {
        Self {
            conf,
            target: target.into(),
        }
    }
    /// Target accessor.
    pub fn target(&self) -> &'s str {
        self.target
    }

    /// Runs vanilla markdown generation.
    pub fn run(&self) -> Res<()> {
        std::fs::create_dir_all(self.target)
            .chain_err(|| format!("during (recursive) folder creation for `{}`", self.target))?;
        let top_level = Self::top_level_md()?;
        log::info!(
            "working on vanilla versions for {} markdown file(s)",
            top_level.len()
        );
        for (idx, file) in top_level.into_iter().enumerate() {
            log::debug!(
                "generating vanilla markdown for `{}` from `{}`",
                file.title,
                file.path,
            );
            self.work_one(idx, file)?;
        }

        log::info!("done with vanilla markdown generation");
        Ok(())
    }

    const SRC: &'static str = "src";
    const SUMMARY: &'static str = "src/SUMMARY.md";

    /// Vector of the top-level markdown files.
    pub fn top_level_md() -> Res<Vec<TopLevelMd>> {
        let mut res = vec![];

        let content =
            load_file(Self::SUMMARY).chain_err(|| format!("on top-level summary file"))?;

        for (idx, line) in content.lines().enumerate() {
            // skip lines that refer no markdown
            if !line.contains("readme.md") {
                continue;
            }
            // skip intro
            if line.contains("Introduction") {
                continue;
            }

            // Expecting a line of shape `- [<NAME>](<PATH>)`
            let err = || {
                err::Error::from(format!(
                    "line {} is illegal, expected `- [<TITLE>](<PATH>)`",
                    idx
                ))
                .chain_err(|| format!("in summary file `{}`", Self::SUMMARY))
            };
            let title_start = line.find('[').ok_or_else(err)? + 1;
            let title_end = line.find(']').ok_or_else(err)?;
            let path_start = line.find('(').ok_or_else(err)? + 1;
            let path_end = line.find(')').ok_or_else(err)?;

            let title = line[title_start..title_end].into();
            let path = line[path_start..path_end].into();

            res.push(TopLevelMd { title, path })
        }

        Ok(res)
    }

    pub fn src_dir(&self) -> PathBuf {
        PathBuf::from(Self::SRC)
    }
    pub fn tgt_dir(&self) -> PathBuf {
        PathBuf::from(self.target)
    }

    /// Works on a single top-level file.
    pub fn work_one(&self, idx: usize, file: TopLevelMd) -> Res<()> {
        let src_path = {
            let mut src_path = self.src_dir();
            src_path.push(&file.path);
            src_path
        };

        let tgt_path = {
            let mut tgt_path = self.tgt_dir();
            let mut tgt_file = format!("{:0>2}_", idx);
            let mut last_is_underscore = true;
            for c in file.title.chars() {
                if c.is_alphanumeric() {
                    tgt_file.push(c);
                    last_is_underscore = false;
                } else if !last_is_underscore {
                    tgt_file.push('_');
                    last_is_underscore = true;
                }
            }
            tgt_file.push_str(".md");
            tgt_path.push(&tgt_file);
            tgt_path
        };

        log::trace!(
            "src_path: {}, tgt_path: {}",
            src_path.display(),
            tgt_path.display()
        );

        let src_content = load_file(&src_path)?;
        let mut tgt_file = open_write(&tgt_path)?;

        for (idx, line) in src_content.lines().enumerate() {
            if line.contains("#include") {
                log::trace!(
                    "inlining line {} of `{}`: {}",
                    idx,
                    src_path.display(),
                    line.trim()
                );
                self.inline_block(&src_path, line, &mut tgt_file)
                    .chain_err(|| {
                        format!(
                            "while inlining code block line {} of `{}`",
                            idx,
                            src_path.display()
                        )
                    })?;
            } else {
                use io::Write;
                let line = if line == "\\" { "<br>" } else { line };
                writeln!(&mut tgt_file, "{}", line).chain_err(|| {
                    format!(
                        "while writing line {} from `{}` to `{}`",
                        idx,
                        src_path.display(),
                        tgt_path.display()
                    )
                })?;
            }
        }

        Ok(())
    }

    pub fn inline_block(
        &self,
        md_path: impl AsRef<Path>,
        line: &str,
        target: &mut impl io::Write,
    ) -> Res<()> {
        let pat = "#include ";
        let err = || err::Error::from(format!("illegal code block include line"));
        let md_path = md_path.as_ref();

        let path_start = line.find(pat).ok_or_else(err)? + pat.len();
        let line = &line[path_start..];
        let path_end = line.find(|c| c == ':' || c == ' ').ok_or_else(err)?;
        let line_tail = &line[path_end..];

        let path = &line[..path_end];

        let code_path = {
            let mut src_path = md_path.to_path_buf();
            let has_parent = src_path.pop();
            if !has_parent {
                bail!("illegal markdown path `{}`", md_path.display())
            }
            src_path.push(path);
            src_path
        };

        let (anchor_start, anchor_end) = if line_tail.starts_with(':') {
            let tail = &line[1..];
            let anchor_end = tail
                .find(|c: char| c == '}' || c.is_whitespace())
                .ok_or_else(err)?;
            let anchor = &tail[..anchor_end];
            (
                Some(format!("ANCHOR: {}", anchor)),
                Some(format!("ANCHOR_END: {}", anchor)),
            )
        } else {
            (None, None)
        };

        log::trace!(
            "code path: {}, anchor: `{}` / `{}`",
            code_path.display(),
            anchor_start.as_deref().unwrap_or("none"),
            anchor_end.as_deref().unwrap_or("none"),
        );

        #[derive(Clone, Copy)]
        enum Mode<'s> {
            Skip { start: &'s str },
            Copy { end: Option<&'s str> },
        }

        let mut mode = if let Some(start) = anchor_start.as_ref() {
            Mode::Skip { start }
        } else {
            Mode::Copy { end: None }
        };
        let code_content = load_file(&code_path)?;

        for line in code_content.lines() {
            match mode {
                Mode::Skip { start } => {
                    if line.contains(start) {
                        mode = Mode::Copy {
                            end: anchor_end.as_deref(),
                        }
                    } else {
                        continue;
                    }
                }
                Mode::Copy { end: Some(end) } if line.contains(end) => {
                    break;
                }
                Mode::Copy { end }
                    if end.is_some()
                        && (line.contains("ANCHOR: ") || line.contains("ANCHOR_END: ")) =>
                {
                    continue;
                }
                Mode::Copy { .. } => {
                    writeln!(target, "{}", line)?;
                }
            }
        }

        Ok(())
    }
}
