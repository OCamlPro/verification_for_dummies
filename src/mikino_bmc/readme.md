# BMC: Mikino

[Mikino][mikino] is a small transition system verification engine that relies on SMT solvers and
everything we have seen so far (and will see later). It is designed to be relatively simple with
user experience front and center: the goal is to have a tool that is gratifying to interact with to
teach about induction-based verification.

Most examples from this point will rely on mikino, so I encourage you to install it so that you can
mess around with my examples and get a better understanding. See the [mikino
appendix](../mikino_install) for setup instructions.

\
\



## Input Format

Mikino takes as input a transition system in a format consistent but slightly different from what
we have seen up to this point. Systems are written in files organized as follows, illustrated on
our stopwatch running example.

First are state variable declarations. It is a list of declarations between braces introduced by
the `svars` keyword and of form `<var_1> <var_2> ... <var_n>: <type>` with `n ≥ 1`.

```rust ,compile_fail,no_run
{{ #include code/sw_1.mkn:var_decls }}
```

Next is the initial predicate, introduced by the `init` keyword. Mikino does not support
SMT-LIB-2-like (s-)expressions (anymore), and instead expects Rust-like expressions. Note that
mikino supports common unicode operators such as `∧`, `⋀`, `∨`, `⋁`, `≥` and `⇒`.

```rust ,compile_fail,no_run
{{ #include code/sw_1.mkn:init }}
```

> Here, we gave `init` a list of three comma-separated (with optional trailing comma) expressions.
> This list is understood as a conjunction `⋀`, meaning the list above is equivalent to writing
> `is_counting = start_stop ⋀ cnt ≥ 0 ⋀ (reset ⇒ cnt = 0)`.

\
\

The transition relation definition, introduced by the `trans` keyword, differs slightly. Remember
that the transition relation relates two states: the *previous* one and the *next* one. In mikino,
we refer to the *previous* version of a state variable `svar` by simply writing `svar`. If we want
to refer to its *next* version, we must use the `'` (prime) prefix operator: `'svar`.

```rust ,compile_fail,no_run
{{ #include code/sw_1.mkn:trans }}
```

> `trans` also accepts a comma-separated list of expressions understood as a *conjunction* `⋀`.

\
\

Last are the candidate invariants, sometimes called **P**roof **O**bjective**s**, introduced by the
`candidates` keyword. They are given as a comma-separated list of named candidates of shape
`"string describing the candidate": <expr>`. The name of a candidate is what mikino will use to
refer to that candidate in its output.

```rust ,compile_fail,no_run
{{ #include code/sw_1.mkn:candidates }}
```

> Mikino's input format is designed to look relatively pretty with Rust syntax highlighting (which
> is used in the snippets above). It is definitely not legal Rust syntax though, so make sure
> `rustfmt` does not run on it as it will fail.

\
\

## Run BMC

Mikino is a proof engine, meaning that it can prove invariants over transition systems as we will
see very soon. For now, let's just use its BMC mode. As discussed previously, BMC is not a proof
technique (at least in infinite reachable state spaces), it is a *refutation* technique: the point
of BMC is to produce counterexamples to candidate invariants thus disproving them.

Let's try mikino on the stopwatch system described above. The full code is available in the
[Version 1](#version-1) section, the following assumes that code is in a `test.mkn` file. Notice
that the candidates

```rust ,compile_fail,no_run
{{ #include code/sw_1.mkn:candidates }}
```

feature `"cnt is positive"`, which we will soon prove is an invariant of the system. Hence,
mikino's BMC will not be able to find a counterexample for this candidate. We are thus going to run
BMC with a *maximum depth*, *i.e.* we will give mikino a maximum number of unrollings to perform:
`10`. The remaining candidates however are falsifiable.

\
\

To put mikino in BMC mode, we need to pass it the `bmc` sub-command when we run it. We will also
use the `--bmc_max <int>` flag that specifies a maximum BMC unrolling depth `≥ 0`. If no maximum is
given, mikino will run BMC until either all candidates are falsified or you end (`Ctrl+C`) the
process manually (or it exhausts memory/time).

\
\

> Mikino requires [Z3][z3] to run, you can retrieve a binary for your operating system on
> [Z3's release page][z3 release]. Mikino, by default, assumes a Z3 binary is in your `PATH` with
> name `z3`. You can override this with the `--z3_cmd` command-line argument: `mikino --z3_cmd
> "my_z3" ...` or `mikino --z3_cmd "./my_z3" ...` if Z3 is not in your `PATH` but is in the current
> directory.

Let's try it. Mikino tries to improve its output's readability by using colors: unfortunately, this
will not show in this plain text rendition. (As discussed when I introduced SMT, different versions
of Z3 or even different operating system might produce different models. The same applies to mikino
as its counterexamples are Z3 models.)

```text
> mikino bmc --bmc_max 10 test.mkn
{{ #include code/sw_1.mkn.out }}
```

> **Pro tip:** use the `--smt_log <DIR>` flag to specify a directory where mikino will create an
> SMT-LIB 2 file per solver it uses, and log all the commands issued to that solver. For instance,
>
> ```text
> > mikino bmc --smt_log smt_traces --bmc_max 10 test.mkn
> > tree smt_traces/
> smt_traces
> └── bmc.smt2
> ```
>
> This can be useful to inspect the exact checks mikino is performing and modify/relaunch them.

Mikino incrementally unrolls BMC just like we discussed in the previous chapter. It starts at depth
`0`, which means *`0` transitions away from the initial states*, which really means *the initial
states*. Right away, it falsifies all our candidates but the first one. This is because of our
initial predicate:

```rust ,compile_fail,no_run
{{ #include code/sw_1.mkn:init }}
```

The system can start with any value for `cnt` as long as *i)* it is positive and *ii)* `reset` is
not pressed. Mikino's output makes sense, but can we modify the system so that falsifiable
candidates can only be falsified by unrolling more than `0` times?

We sure can, by changing `init` so that `cnt` always starts at `0`.

```rust ,compile_fail,no_run
{{ #include code/sw_2.mkn:init }}
```

We do not need to look at `reset` anymore since `cnt` will be `0` regardless. The full code for
this new version is available in the [Version 2](#version-2) section. We run mikino in BMC mode
again, and this time we get

```text
> mikino bmc --bmc_max 10 test.mkn
{{ #include code/sw_2.mkn.out }}
```

Mikino is not able to falsify the falsifiable candidates in the initial states (depth `0`, *i.e.*
zero unrollings of the transition relation) anymore, which was the whole point of the modification
to `init` we just made. Mikino proceeds to check for falsifications at increasing depth. Once it
reaches depth `3`, a falsification for `cnt ≤ 2` is found and a counterexample is produced. The
counterexample shows the whole trace, from an initial state to a state falsifying the candidate
because `cnt = 3` and `3 ≤ 2` is not `true`.

Mikino keeps going with the remaining candidates. Although it does not appear in the output, after
finding a counterexample at depth `3` mikino checks the remaining candidates (without `cnt ≤ 2`) at
depth `3`. We got one counterexample for one candidate, but there might be a different
counterexample for another candidate at the same depth.

This is not the case here, and mikino proceeds to unroll the transition relation some more. It
finds another counterexample at depth `5` for `cnt ≤ 4` and displays the whole trace, as expected.

\
\

Let's modify our candidates, full code available in the [Version 3](#version-3) section.

```rust, compile_fail,no_run
{{ #include code/sw_3.mkn:candidates }}
```

You can place your bets as to which of these candidates are actual invariants. The third candidate
is a bit strange, we will discuss why it is written that way shortly. Again, BMC cannot prove that
any of them are indeed invariants, but it can disprove some of them if it finds a counterexample at
some depth.

```text
> mikino bmc --bmc_max 10 test.mkn
{{ #include code/sw_3.mkn.out }}
```

Candidate `is_counting implies cnt > 0` was falsified. The idea of this candidate is that, when the
system `is_counting`, `cnt` should increase and thus be strictly positive (more on that in the note
below). Mikino shows us this is not true however, because `reset` has higher priority in our
transition relation and causes `cnt` to be `0` regardless of `is_counting`'s value.

\
\

> We had to somewhat artificially write the candidate as `(is_counting ⋀ ¬start_stop) ⇒ cnt > 0`.
> Based on the paragraph above, the `is_counting ⋀ ¬start_stop` part should really be
> `is_counting`. The problem with this is that we actually ignore `is_counting` in the initial
> state.
>
> Hence, we would get a initial state counterexample where `start_stop` is `true`, meaning
> `is_counting` is `true`, but `cnt` ignores it and is just `0`. As authors, we wanted to show a
> counterexample where `reset` prevents `cnt` from increasing despite `start_stop` being `true`,
> and thus had to distort the candidate a little bit.
>
> A better way to write this candidate is `is_counting ⇒ 'cnt > cnt`. It would still be
> falsifiable, for the same reason and with the same counterexample, but it would make more sense.
> Sadly, mikino does not **currently** support *"two-state candidates"*, *i.e.* candidates that
> refer to a *previous* state.
>
> Checking two-state candidates differs slightly from regular (one-state) candidates in that they
> make no sense in the initial states (depth `0`) because there is no previous state there. Hence,
> a two states invariant defined as `two_state_expr` is understood as being the expression `true`
> in the initial states (which holds, obviously), and `two_state_expr` at depth `> 0` since there
> is a previous state to refer to.

\
\

## Full Code for All Examples

### Version 1

<details>
	<summary>Expand this for the full code.</summary>

```rust ,compile_fail,no_run
{{ #include code/sw_1.mkn:all }}
```

Output:

```text
> mikino bmc --bmc_max 10 test.mkn
{{ #include code/sw_1.mkn.out }}
```
</details>

### Version 2

<details>
	<summary>Expand this for the full code.</summary>

```rust ,compile_fail,no_run
{{ #include code/sw_2.mkn:all }}
```

Output:

```text
> mikino bmc --bmc_max 10 test.mkn
{{ #include code/sw_2.mkn.out }}
```
</details>

### Version 3

<details>
	<summary>Expand this for the full code.</summary>

```rust ,compile_fail,no_run
{{ #include code/sw_3.mkn:all }}
```

Output:

```text
> mikino bmc --bmc_max 10 test.mkn
{{ #include code/sw_3.mkn.out }}
```
</details>

[z3]: https://github.com/Z3Prover/z3 (Z3 on github)
[z3 release]: https://github.com/Z3Prover/z3/releases (Z3's releases on github)
[rust]: https://www.rust-lang.org/tools/install (Rust website, installation)
[mikino]: https://github.com/OCamlPro/mikino_bin (Mikino on github)
[release page]: https://github.com/OCamlPro/mikino_bin/releases
(Mikino's release page on github)
