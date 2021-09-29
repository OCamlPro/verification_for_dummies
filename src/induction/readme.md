# Induction

Let's get a little bit abstract and meta. The incremental BMC approach we have seen in previous
chapters can itself be seen as a transition system. To do this formally, we would need a whole
bunch of notions from logics which are far beyond this book's scope. No matter, we can discuss
BMC as a transition system informally, with words. Writing *counterexample* constantly is quite
tedious, we will use the much shorter *cex* (plural *cex-s*) contraction instead. Also, assume
there is only one candidate for simplicity.

\
\

We can see BMC as having a state: the unrolling depth `k` from the initial state at which it
currently is. We can say it produces a boolean output that's `true` if a cex for the candidate
exists at depth `k`. BMC's starting point is *"check the initial states for a cex (of the
candidate)"*, which we can rephrase as

- `init`: unroll the system at depth `0` from the initial state and check for cex.

A BMC *transition* amounts to unrolling the transition relation one step further (depth `k`), and
check for falsification at `k`. Rephrased to echo `init`'s formulation, we get

- `trans(k-1, k)`: from an unrolling at `k-1` from the initial states with no cex, unroll to `k`
  and check for a cex (with `k > 0`).

So now we have a representation of BMC as a transition system with its `init` predicate and `trans`
relation.

\
\

It would be interesting to find a candidate invariant for BMC and try to prove it over the
transition system representation of BMC we just introduced. As some readers have probably intuited,
BMC actually has the property that it always finds the shortest cex possible in terms of *depth*
(number of unrollings). More precisely, it finds one of them: if BMC produces a cex (trace of `k`
states) of length `k`, there might be other cex-s of length `k` (and of length `i > k`). However,
there cannot exist a shorter cex (of length `i < k`). More generally:

- `candidate(k)`: when BMC is unrolled at `k` from the initial states, then no cex of length `0 ≤ i
  < k` exists.

To be clear, our goal is to find a way to prove that `candidate` is an invariant for BMC, which
is represented as a transition system by the `init` predicate and `trans` relation above.

\
\

The question now is *"How can we prove that BMC verifies `candidate`?"*, or *"What would such a
proof look like?"*. Back when we discussed transition system, we managed to prove a few properties
regarding the stopwatch system's transition relation. For instance, we previously proved that
assuming `cnt_0 > 7`, then we cannot have `cnt_1 = 0` without `reset_1` being `true` if state `1`
is a successor of state `0`.

So we could start building a proof for `candidate` by checking if it is a *consequence* of `trans`:
is it true that `trans(k-1, k) ⇒ candidate(k)`?. Let's assume we have an unrolling at depth `k-1`
from the initial states with no cex; by `trans`, the next BMC step is to unroll to `k` and check
for a cex at `k`. Looking at `candidate` now, is it the case that no cex of length `i < k` can
exist?

Well no, looking only at the assumptions we made we cannot draw that conclusion: `trans` tells us
there is no cex at `k-1`, but that's it. We know nothing of potential cex-s at `i < k - 1`. So,
`candidate` is not a *consequence* of `trans`. All hope is not lost: our tiny proofs over the
stopwatch system actually made assumptions about the *previous* state. "**Assuming** `cnt_0 > 7`,
then we cannot have `cnt_1 = 0` without ..."

\
\

Instead of checking if `candidate` is a *consequence* of `trans` (which it is not as we just saw)
we could check `trans` *preserves* `candidate`. Since `trans` relates succeeding states `k-1` and
`k`, we say that `trans` *preserves* `candidate` if `candidate(k) ∧ trans(k-1, k) ⇒ candidate(k)`.
That is, *"states verifying `candidate` cannot, in one application of `trans`, reach a state
falsifying `candidate`"*.

Is it the case though? We take the same assumptions as above, when we looked at a transition from
`k-1` to `k`, and also assume `candidate` at `k-1`: *"no cex of length `i < k-1` exists"*. By
`trans`, we unroll to `k` and check for a cex at `k`. Can there be cex of length `i < k`? No:
`trans` tells us there was no cex at `k-1`, and our new `candidate`-assumption in the previous
state tells us no cex of length `i < kh-1 ` exists.

\
\

Sweet, `trans` preserves `candidate`: from a state verifying `candidate`, we can only reach states
that also verify `candidate`. Hence, a state verifying `candidate` *cannot lead* to a state
falsifying it by repeated applications of `trans`. Is this enough to decide `candidate` to be an
invariant for BMC? No, unless we show all our initial states verify `candidate`.

Imagine for instance we got BMC wrong and started at depth `1` instead of `0`, with exactly the
same `trans`. Then, since we never checked for a cex at `0`, `candidate` has no reason to be true
at `1`. More generally, if our initial states do not all verify `candidate`, then the fact that
`trans` preserves `candidate` is not helpful because it says nothing about transitions from a
state that does **not** verify `candidate`.

Do(es) BMC's initial state(s) verify `candidate` then? That is, when BMC is unrolled at `0` from
the initial states, is it possible that a cex of length `i` with `0 ≤ i < 0` exists? Well, since
there is no `i` such that `0 ≤ i < 0`, then no.

\
\

Putting both results together we have

- BMC's starting point verifies `candidate`, *i.e.* `init ⇒ candidate(0)`, and
- BMC's notion of transition preserves `candidate`, *i.e.* `candidate(k-1) ∧ trans(k-1, k) ⇒
  candidate(k)`.

Then, by *induction*, executions of BMC cannot ever falsify `candidate`.


## One Last Short SMT Dive

To sum up, given a transition system `𝕋` with state variables `s` and specified by `(init(s),
trans(s, s'))`, we can invoke *induction* to prove that `candidate(s)` is an invariant for `𝕋` if
we have shown both *base* and *step*:

- *base*: for all `s`, `init(s) ⇒ candidate(s)`;
- *step*: for all `s` and `s'`, `candidate(s) ∧ trans(s, s') ⇒ candidate(s')`.

We can rephrase these two in terms of SMT solving and formula (un)satisfiability:

- *base*: `init(s) ∧ ¬candidate(s)` is unsatisfiable;
- *step*: `candidate(s) ∧ trans(s, s') ∧ ¬candidate(s')` is unsatisfiable.

We all know what this means: it is finally time to achieve our dream of proving that the
stopwatch's counter is always positive. I will use the version that starts from `cnt = 0`, not the
one where it can take an arbitrary positive value. Both versions work for this proof, but the
former is better for obtaining non-trivial (length `0`) counterexamples if we need to.

> Readers eager to *learn by doing* can start from any of the previous SMT examples involving BMC
> and try to conduct the proof themselves. The SMT examples for BMC have definitions for both
> `init` and `trans` ready to use. The easy version consists in having an SMT-LIB script for the
> *base* case, and another one for the *step* case. Solution in the [Stopwatch
> Base](#stopwatch-base) and [Stopwatch Step](#stopwatch-step) sections.
>
> Bonus points if you can do both with just one script, using activation literals. Perfect score if
> you can do both checks using only one activation literal, **solely** for the purpose of
> (de)activating `init`.
>
> Perfect score solution in the [Stopwatch Actlit](#stopwatch-actlit) section.

\
\

### Base

SMT examples for BMC from previous chapters already have definitions for the stopwatch's `init` and
`trans`. For convenience and readability, we define a `candidate` predicate over the system's
counter:

```text
{{ #include code/sw_base_1.smt2:cand_def }}
```

In the *base* check, we are only concerned with the initial states. All we need to do

- is declare our state variables,
- assert that they are a legal initial state,
- assert that they falsify our candidate, and
- ask whether this is satisfiable.

```text
{{ #include code/sw_base_1.smt2:main }}
```

Z3 easily answers our question.

> Full code in the [Stopwatch Base](#stopwatch-base) section below.

```text
> z3 test.smt2
{{ #include code/sw_base_1.smt2.out }}
```

Done: we proved the *base* case, *step* is next, let's move on.

\
\

### Step

For the *step* check, which we are doing separately (in a different file) from *base*, we first
need to declare two states since we need to check that `trans` preserves `candidate`.

```text
{{ #include code/sw_step_1.smt2:var_decls }}
```

Next, we want to ask whether it is possible to have

- state `0` verify `candidate`,
- state `1` be a successor of state `0`, and
- state `0` falsify `candidate`.

```text
{{ #include code/sw_step_1.smt2:main }}
```

And that's it. Unless Z3 decides to answer `sat` for some reason, we are done.

> Full code in the [Stopwatch Step](#stopwatch-step) section below.

```text
> play drumroll.wav
> z3 test.smt2
{{ #include code/sw_step_1.smt2.out }}
```

Done and done. Both *base* and *step* hold, and thus we can finally invoke induction and conclude
that `cnt ≥ 0` is an invariant for the stopwatch system.

Before we move on to mikino's induction mode, some readers might want to check out Section
[Stopwatch Actlit](#stopwatch-actlit) below. In it, we conduct *base* and *step* in succession in a
single file using an activation literal. That's not all we do however, there is a clever trick that
we use for the checks. The trick is discussed in details in the comments.

\
\

### Full Code For All Examples

#### Stopwatch Base

<details>
	<summary>Expand this for the full code.</summary>

```text
{{ #include code/sw_base_1.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_base_1.smt2.out }}
```
</details>

#### Stopwatch Step

<details>
	<summary>Expand this for the full code.</summary>

```text
{{ #include code/sw_step_1.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_step_1.smt2.out }}
```
</details>

#### Stopwatch Actlit

<details>
	<summary>Expand this for the full code.</summary>

Until now, we performed the *step* check of an induction proof by giving ourselves a state `0` and
a state `1` such that
- `trans(s_0, s_1)`: state `1` is state `0`'s successor,
- `candidate(s_0)`: state `0` verifies the candidate,
- `¬candidate(s_1)`: state `1` falsifies the candidate.

Now, the example below swaps the state indices `0` and `1`. That is:
- `trans(s_1, s_0)`: state `0` is state `1`'s successor,
- `candidate(s_1)`: state `1` verifies the candidate,
- `¬candidate(s_0)`: state `0` falsifies the candidate.

This does not really change anything by itself, the check is same except that the indices have
changed. We do need to be careful to extract the counterexample correctly though.

The reason we present this version is that this *reverse-unrolling* version lets us keep state `0`
as the *last state of the trace*, *i.e.* the state on which the falsification occurs. In normal
unrolling, if we wanted to unroll the transition relation more, we would need to introduce `s_2`,
deactivate `¬candidate(s_1)`, assert `candidate(s_1)`, and conditionally assert `¬candidate(s_2)`.

With reverse-unrolling we can just say `s_2` is `s_1`'s previous state, and assert
`candidate(s_2)`. We are not unrolling more than once here (a process called `k`-induction), but
this reverse-unrolling trick is still convenient *w.r.t.* the *base* check. The *base* check asserts
`¬candidate(s_0)`, which *step* also needs.

```text
{{ #include code/sw_actlit_1.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_actlit_1.smt2.out }}
```
</details>
