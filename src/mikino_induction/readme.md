# Induction: Mikino and Step Cex-s

BMC is not the only thing mikino can do. It also has an induction mode which is activated with the
`check` sub-command.

> **Pro tip:** remember the `--smt_log <DIR>` flag from mikino's `bmc` mode? It specifies a
> directory where mikino will create one SMT-LIB 2 file per solver it uses, and log all the commands
> issued to that solver. Mikino's `check` mode has it too:
>
> ```text
> > mikino check --smt_log smt_traces test.mkn
> > tree smt_traces/
> smt_traces
> ├── base.smt2
> └── step.smt2
> ```
>
> This can be useful to inspect the exact checks mikino is performing and modify/relaunch them.

Let's make sure mikino is able to prove that `cnt ≥ 0` on the stopwatch system. I am using the
version of the system that starts at `0`

```rust ,compile_fail,no_run
{{ #include code/sw_1.mkn:init }}
```

with a `cnt ≥ 0` candidate as well as a few falsifiable other candidates:

```rust ,compile_fail,no_run
{{ #include code/sw_1.mkn:candidates }}
```

\
\

Let's run mikino in `check` mode on this system, full code in the [Full Code](#full-code) section.

```text
> mikino check test.mkn
{{ #include code/sw_1.mkn.out }}
```

Looking just at the final result, mikino is telling us that all candidates hold in the initial
state(s). So, the *base* part of the induction proof holds for all candidates. Next, mikino reports
that two of the candidates are not preserved by the transition relation. Since the *check* part of
the induction proof does not hold for these candidates, mikino does not know whether they hold and
tells us that the system **might** be unsafe. Based on the checks mikino performed, it cannot
decide whether they are invariants or not.

Last, mikino reports that `cnt is positive` is actually preserved by the transition relation
meaning *step*, in addition to *base*, holds for this candidate. Mikino can thus conclude that it
is an invariant for the system.

\
\

If we take a closer look at mikino's output during the *step* checks, we see that mikino is doing
more that just saying some *step* checks failed. When they do, mikino also outputs a *step
counterexample (cex)*. Remember what a *step* check is: for any state `k`

- assuming state `k` verifies `candidate`,
- assuming state `k+1` is a successor of state `k`,
- is it possible that state `k+1` falsifies `candidate`?

If it is possible, it means that there exists a state `k` verifying `candidate` which has a
successor state `k+1` falsifying `candidate`. Under the hood, this means the solver answered `sat`
to mikino's *step* `check-sat` query, meaning mikino can invoke `get-model` for *step cex*: a pair
of succeeding states showing that `candidate` is not necessarily preserved by the transition
relation.

For candidate `cnt ≥ 2` for instance, mikino lets us know that from a state where `cnt = 2` which
verifies the candidate, it is possible in one transition to reach a state where `cnt = 3` which
falsifies the candidate. Mikino gives us the values of all state variables so that we know how
precisely the *bad* state can be reached. There might be more than one step cex, as is the case for
candidate `cnt ≥ 2`: mikino (the SMT solver, really) decides to start counting in step `k+1` in the
step cex, but we could get the same result if we were already counting in step `k`.

\
\

This notion of step cex is important because, on real systems, candidates tend not to be inductive.
We will discuss this in the next chapter, but a candidate can be an invariant without being
inductive. There are various ways we can go about proving that a non-inductive candidate is an
invariant, but most of them (including the one we will discuss soon) involve manually or
automatically looking at step cex-s to understand why the candidate is not inductive and *"act"*
accordingly. (The meaning of *"act"* depends on the actual technique used to get around
non-inductiveness.)

\
\

## Run BMC, Again

We can change the mikino command we used to instruct mikino to run BMC on the candidates it failed
to prove. For instance, `mikino check --bmc test.mkn` will run BMC after the proof attempts in an
attempt to falsify remaining candidates. More precisely, this command will run BMC without a
maximum unrolling depth.

On this simple example, we already know the remaining candidates are falsifiable in a small number
of transitions. When we do not have this information, it can be a good idea to specify a maximum
unrolling depth with `--bmc_max <int>` just like we did in `bmc` mode. Note that using the
`--bmc_max` flag automatically activates BMC, so we don't need the `--bmc` flag anymore.

On our example

```rust ,compile_fail,no_run
{{ #include code/sw_1.mkn:candidates }}
```

the last two candidates should be falsifiable at depth `3` and `5` respectively. Let's make sure
this is the case.

```text
> mikino check --bmc_max 5 test.mkn
{{ #include code/sw_2.mkn.out }}
```

## Full Code

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
