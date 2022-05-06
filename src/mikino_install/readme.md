# Appendix: Mikino

Mikino is written in [Rust][rust] and is available as a Rust library

- https://crates.io/crates/mikino_api
- https://docs.rs/mikino_api/0.9.1/mikino_api

and a Rust birany

- https://crates.io/crates/mikino

So, if you already have Rust installed on your system (or don't mind [installing it][rust install])
just make sure it is up-to-date and ask `cargo` to install mikino for you.

```bash
# update rust
> rustup self update
> rustup update

# install mikino, `-f` allows overwriting (updating)
# the previous mikino install if any
> cargo install -f mikino
```

\
\

Otherwise, head to [mikino's release page][mikino release] and download the latest release for your
operating system. The only other alternative is to [build mikino from scratch](#build).

\



## Z3

Mikino requires [the Z3 SMT solver][z3]. You can build it from source or recover a binary from the
[release page][z3 release].

From this point forward I assume readers have a Z3 binary called `z3` in their path. That is,
running the command `z3 -version` should not fail and produce an output similar to

```text
Z3 version 4.8.13 - 64 bit
```

Mikino, by default, assumes a Z3 binary is in your `PATH` with name `z3`. You can override this
with the `--z3_cmd` command-line argument: `mikino --z3_cmd "my_z3" ...`, or `mikino --z3_cmd
"path/to/my_z3" ...` if Z3 is not in your `PATH`.

\

Note that other efficient solvers exist such as [Alt-Ergo][ae], [CVC4][cvc4] and [Yices 2][yices].
Solvers tend to be perform well on different kinds of problem, and verification frameworks
routinely run several of them in parallel, wait for the quickest answer, and discard solver
instances that are still running.

\



## Build

You can also build mikino, it's actually quite easy. [Install Rust][rust install] or make sure it
is up-to-date if it is installed already.

```bash
# update rust
> rustup self update
> rustup update
```

Clone [mikino's (binary) repo][mikino repo], and `cargo build` it:

```bash
> clone https://github.com/OCamlPro/mikino_bin
> cd mikino_bin

# debug, unoptimized build
> cargo build
> ./target/debug/mikino -V
mikino 0.9.1

# release, optimized build
> cargo build --release
> ./target/release/mikino -V
mikino 0.9.1
```

Alternatively, you can ask `cargo` to install your local clone of the repo:

```bash
> clone https://github.com/OCamlPro/mikino_bin
> cargo install --path mikino_bin
> mikino -V
mikino 0.9.1
```



[rust]: https://www.rust-lang.org
[rust install]: https://www.rust-lang.org/tools/install
[mikino release]: https://github.com/OCamlPro/mikino_bin/releases
[mikino repo]: https://github.com/OCamlPro/mikino_bin
[z3]: https://github.com/Z3Prover/z3
[z3 release]: https://github.com/Z3Prover/z3/releases
[ae]: https://alt-ergo.ocamlpro.com (Alt-Ergo homepage)
[cvc4]: https://cvc4.github.io/ (CVC4 homepage)
[yices]: https://yices.csl.sri.com (Yices 2 homepage)
