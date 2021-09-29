# Unrolling and BMC

> Here we finally start doing things. We will perform a kind of analysis called BMC. While not a
> proof technique in general, it is a very useful *falsification* technique and paves the way
> towards *induction*.

In the previous chapter, we played with our running example using Z3 by

- defining the transition relation as a `define-fun`,

<details>
	<summary>Expand for a refresher on this definition.</summary>

```text
{{ #include ../trans_smt/code/sw_trans_1.smt2:trans_def }}
```
</details>

- declaring two states `0` and `1`,

<details>
	<summary>Expand for a refresher on these declarations.</summary>

```text
{{ #include ../trans_smt/code/sw_trans_1.smt2:states_def }}
```
</details>

- asserting the transition relation between state `0` and state `1`, and

<details>
	<summary>Expand for a refresher on this assertion.</summary>

```text
{{ #include ../trans_smt/code/sw_trans_1.smt2:unroll_1 }}
```
</details>

- querying Z3 by constraining state `0` and/or state `1` to inspect the transition relation and
  prove some basic properties over it.

<details>
	<summary>Expand for the last assertion and the queries.</summary>

```text
{{ #include ../trans_smt/code/sw_trans_1.smt2:state_constraints }}
```
</details>

\
\

## Unrolling

Now, this process of asserting the transition relation between two states `0` and `1` effectively
enforces the constraint that state `1` must be a legal successor of state `0`. This process is
called *unrolling the transition relation*, or *unrolling the system*, or just *unrolling*.

So far, we have only unrolled once to relate state `0` and state `1`. We can unroll more than once,
simply by declaring more states and relate `0` to `1`, `1` to `2`, *etc.* by asserting the
transition relation over the appropriate state variables.

<details>
	<summary>Expand for an example of unrolling the system thrice.</summary>

```text
{{ #include code/sw_unroll_1.smt2 }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_unroll_1.smt2.out }}
```
</details>

\
\

## Reachability

Before we actually get to BMC, let's define a few notions. Remember that transition systems have
state variables, and that a *state* is a valuation of all these state variables. Let's say a state
`s` is *reachable* if the system, starting from one of its initial states, can reach `s` by
applying its transition relation `n` times, where `n` is an arbitrary natural number.

> Note that `n` can be `0`, *i.e.* the initial states of a system are reachable, naturally.

This notion of *reachability* is usually extended to apply to state predicates. For instance, in
the stopwatch system, we can say that the state predicate `cnt > 5` is reachable: just start from
`0` and keep counting.

\
\

Using this notion, we can talk about the set of all reachable states for a given system, called its
*reachable state space*. This set can be infinite, and even when it's not, actually constructing
this set for realistic systems tends to be impractical. A tool that tries to construct this set is
called *explicit-state*. SMT-based approaches are almost always *implicit-state*, as SMT solvers
reason at theory-level about booleans, integers... directly to assess whether a given formula is
satisfiable. The only time actual values (and thus states) are produced is when the formula is
satisfiable and we ask for a model.

> While generally inefficient, tools such as [TLA+] do manage to scale the explicit-state approach
> to impressively large systems. Also, it should be noted that when such a tool manages to
> terminate, *i.e.* compute the entire reachable state space, they are able to (dis)prove
> properties that are much more complex than anything we will do here. [TLA+] for instance can
> reason about *linear temporal logic* formulas which are far beyond the scope of this book.

\
\

Let's introduce one more notion, that of *invariants*. Given some transition system, we can write
down a state predicate (such as `cnt ≥ 0`) and wonder whether it *holds* (evaluates to `true`) on
all reachable states. If it does, then that state predicate is an *invariant* of the system, or
*holds* for the system.

From now on, we will be interested in transition systems with some *candidate invariants*. That is,
we will have *"properties"* and we will have to (dis)prove that they are invariants for the system.
We will say a system is *safe* if all the candidate invariants are actually invariants. Otherwise,
the system is *unsafe*.

\
\

## Fantastic Counterexamples and How to Find Them

When a candidate invariant `I` is not an actual invariant, it means there is *at least* one
reachable state `s` that *falsifies* `I`, *i.e.* `I(s)` evaluates to `false`. Since `s` is
a reachable state, it means that there exists a trace of states `s_0`, `s_1`, ... `s_n` such that

- `s_0` is an initial state, meaning `init(s_0)` is `true`,
- `∀ i ∈ [0, n[`, `s_i+1` is a successor of `s_i`, meaning `trans(s_i, s_i+1)` is `true`, and
- `s_n = s`, meaning `I(s_n)` is `false`.

Assuming we are reporting to someone/something, we want to do better than just say `unsafe` when a
candidate invariant does not hold for the system. Ideally, we should produce a witness of the
candidate's falsification: a *counterexample*, which would be a trace of succeeding states leading
to a state falsifying the candidate.

\
\

Thankfully, we have an SMT solver to do this. Can we actually explore the reachable state space and
look for a falsification given what we have seen so far?

A first approach to doing this would be to write a bunch of assertions that are satisfiable if and
only if there exists such a counterexample trace of some arbitrary length. Unfortunately, we cannot
really do this as unrolling is a manual process: we declare state `i`, then assert the relation
between state `i-1` and state `i`. We cannot write a finite number of assertions that encode an
arbitrary number of unrollings for the SMT solver to reason about. You can go ahead and try it, but
it will not work. At least not without quantifiers (`∀`, `∃`), which would not scale well at all.

\
\

Now that we are frustrated by this dead-end approach, let's forget about our ideal goal and try
tackle something simpler: can we look for a falsification of the candidate invariants in the
initial states?

Let's get back to our running stopwatch example, and add a candidate invariant: `cnt ≥ 0`. Recall
that the stopwatch's initial predicate is

```text
init(s) ≜ (s.reset ⇒ s.cnt = 0) ∧ (s.is_counting = s.start_stop)
```

\
\

Now, we need to design some assertions for the SMT solver such that they are satisfiable if and
only if there exists an initial state that falsifies our candidate. This is quite similar to the
unrolling we did in the previous chapter, where we wrote assertions that were satisfiable if and
only if state `1` was a successor of state `0`, and `cnt_1` was something else than `0`, `cnt_0` or
`cnt_0 + 1`.

Following the same approach, we first need to `define-fun` our initial state predicate.

```text
{{ #include code/sw_init_1.smt2:init_def }}
```

That was easy. Next up, declare a state so that we can assert `init` on it.

```text
{{ #include code/sw_init_1.smt2:states_def }}
```

Then we write the `init` assertion.

```text
{{ #include code/sw_init_1.smt2:assert_init }}
```

So easy. We want the SMT solver to look for a falsification of our candidate `cnt ≥ 0`, so we just
assert that.

```text
{{ #include code/sw_init_1.smt2:state_constraints }}
```

If Z3 answers `sat` to these constraints, it means it found some values for the state variables
such that they

- represent an actual initial state, and
- falsify our candidate.

> Full code in the [Version 1](#version-1) section below.

```text
> z3 test.smt2
{{ #include code/sw_init_1.smt2.out }}
```

Did it work? Let's look at our initial predicate again:

```text
init(s) ≜ (s.reset ⇒ s.cnt = 0) ∧ (s.is_counting = s.start_stop)
```

The specification of the system did not really say anything about the initial value `cnt` should
have. At least not besides the fact that it should be `0` when `reset` is `true`. Hence, when
`reset` is `false`, `cnt` is not constrained in any way. In a real program, one could see this as a
*use-before-init* problem where we declare (but not initialize) a `cnt` variable, set it to `0` if
`reset` is `true`, but do nothing otherwise: `cnt` could be anything (including an invalid integer).

\
\

So our system is unsafe: the candidate does not hold. The specification was not precise enough.
Let's say from now on that the specification tells us *`cnt` is initially an arbitrary positive
integer*. Let's fix our initial predicate.

```text
{{ #include code/sw_init_2.smt2:init_def }}
```

We do not need to change anything else, we can just run the same check on the updated initial
predicate.

> Full code in the [Version 2](#version-2) section below.

```text
> z3 test.smt2
{{ #include code/sw_init_2.smt2.out }}
```

Perfect: by answering `unsat`, Z3 is telling us that it proved that no valuation of `s_0` is such
that it is an initial state and it falsifies the candidate invariant. We just proved something: no
falsification of the candidate is reachable in `0` transitions. Nice.

Can we keep going? Is the candidate falsifiable in `1` transitions, or `7`, or more? Of course we
can, thanks to unrolling. We previously used unrolling to start from some arbitrary state `s_0` and
perform checks about its potential successor(s). If we just force `s_0` to be initial, like we just
did, we can then unroll once to ask Z3 whether a successor `s_1` of `s_0` can falsify the
candidate. If not, we can unroll once more, and so on until we find a falsification.

Congratulations to us, we just invented BMC.

\
\

> The stopwatch system has an infinite reachable state space since `cnt` can reach any integer
> value (just keep incrementing it). Start actually proving candidates in the next chapter, this
> one focuses solely on finding counterexamples.

\
\

## BMC

**B**ounded **M**odel-**C**hecking (BMC) is a *forward exploration* of the reachable state space of
a transition system. The term *forward exploration* refers to the fact that BMC starts from the
initial states and explores the state space by unrolling the transition relation incrementally.

As a technique **B**MC is explicitly *bounded*: it explores the reachable state space **up to
some** depth (number of unrollings). That is, as long as the reachable state space is infinite, BMC
cannot prove anything because it will never finish exploring the state space. All it can do is
*disprove* candidates.

\
\

By this point, I expect most readers to be able to write SMT-LIB code that corresponds to a BMC
check for a given number of unrollings. Just to make sure, the [BMC with
Unrolling](#bmc-with-unrolling) section showcases a BMC check where the transition relation is
unrolled twice.

\
\

> **Warning:** slightly (more) technical and practical discussion ahead. What follows is not
> mandatory to understand the upcoming chapters, but I think it is quite interesting and definitely
> mandatory for writing your own (efficient) verification engine.

\
\

Let's discuss a few practical points regarding BMC. Mainly, the fact that it is incremental and
that what we do at a given step depends on the solver's previous answer. For instance, say we have
several candidate invariants and we are checking whether we can falsify some of them by unrolling
`k` times. Say also the solver answers yes (`sat`) and gives us a model. Then what we want to do is
check which candidates are falsified (using the model), and keep BMC-ing the candidates that were
not falsified. We got a counterexample for some of the candidates, but there might be a different
counterexample at the same depth falsifying other candidates. If not (`unsat`), we move on and
check the remaining candidates at `k+1` and so on. Maybe they can be falsified by unrolling more
than `k` times.

So, this whole process is interactive: what BMC does depends on what the solver previously said. In
the next chapter, I will introduce mikino which is a tool that will perform BMC (and more) for us.
The way mikino conducts BMC is by launching Z3 as a separate process and feed it definitions,
declarations, assertions, `check-sat`s and `get-model`s on its standard input. Z3 produces answers
on its standard output, which mikino looks at to decide if/how to continue and what to stream to
the input of the Z3 process.

\
\

Based on what we have done so far, this would require restarting the solver each time. Say Z3
answers `unsat` when we unroll `k` times. It means that we have an assertion of the negation of the
candidate(s) for `s_k` which made our whole SMT-LIB instance (all the assertions together) `unsat`:
`(assert (not (candidate s_k)))`. Now, this assertion is only there for our check at depth `k`, to
ask for a falsification of the candidate(s). Still, we cannot move on and unroll at `k+1`: this
assertion will still be there, and the instance will remain `unsat`.

So, instead of restarting Z3, we can make the assertion of the negation of the candidates
conditional. That is, we can give ourselves a *boolean flag* that *activates* this assertion.
Such a flag is called an *activation literal*, or *actlit*.

Say we are performing a BMC check at depth `k`. First, we need to declare this *"boolean flag"*.

```text
(declare-const actlit_k Bool)
```

Next, we write our assertion of the negation of the candidate(s) in such a way that `actlit_k`
needs to be true for the assertion to be active.

```text
(assert
	(=> actlit_k
		(not (and (candidate_1 s_k) (candidate_2 s_k) ...))
	)
)
```

Notice that if `actlit_k` is `false`, then this assertion is trivially `true` and thus does not
contribute to whether other assertions are satisfiable. This is because `false ⇒ P` is always
`true`, regardless of what `P` is. In particular, `false ⇒ false` is true.

The last thing we need now is to perform a `check-sat` *assuming* `actlit_k` is true. We could
`(assert actlit_k)` but that would not solve our problem: we cannot go back and *undo* this
assertion, hence the negation of the candidates is active, hence the whole instance is `unsat`.

\
\

Instead, we can use the `check-sat-assuming` SMT-LIB command. This command takes a list of boolean
variables and forces to `check-sat` our assertions **assuming** these variables are `true`, but
**without** actually asserting them. Meaning that, after the check-sat, these variables are still
unconstrained.

In particular, it means we can perform a `check-sat-assuming` on `actlit_k`, and then just assert
`actlit_k` to be false to effectively deactivate the assertion of the negation of the candidates.

\
\

This is all a bit abstract, let's see it in action on the stopwatch system. The [BMC with
Unrolling](#bmc-with-unrolling) section shows an unrolling of the system at depth `2` with the
corresponding check for candidate `cnt ≥ 0`, and just that check. Let's modify it so that it uses
activation literals to perform all checks up to depth `2`.

The first check to perform is at depth `0`, so all we asserted so far is that state `0` is initial.

```text
{{ #include code/sw_actlit_1.smt2:assert_init }}
```

Next we declare our activation literal for the upcoming check.

```text
{{ #include code/sw_actlit_1.smt2:actlit_0_decl }}
```

Then we conditionally assert the negation of the candidate.

```text
{{ #include code/sw_actlit_1.smt2:actlit_0_assert }}
```

Then comes the check itself, using the brand new `check-sat-assuming` command we just discussed.

```text
{{ #include code/sw_actlit_1.smt2:actlit_0_check_sat }}
```

Notice the use of the `echo` command which takes a string and causes the solver to output said
string to its standard output. Remember that we will perform more than one check, so we use `echo`
to keep track of what question the `sat`/`unsat` answers are for.

As we already saw, this check will produce `unsat`: there is no falsification of this candidate at
depth `0` (or at any depth, but we have not proved that yet).

```text
{{ #include code/sw_actlit_1.smt2:deactlit_0 }}
```

As a sanity check, we can `check-sat` right after we deactivated `actlit_0`. We just got an `unsat`
because we assumed `actlit_0`, so if the deactivation of the negation of the candidate failed then
a regular `check-sat` would also yield `unsat`. If deactivation worked, we should get `sat` because
`(init s_0)`, our only active assertion, is `sat`.

```text
{{ #include code/sw_actlit_1.smt2:sanity }}
```

We can now keep on unrolling and `check-sat-assuming`, since the assertion of the negation of the
candidate should now be deactivated.

```text
{{ #include code/sw_actlit_1.smt2:depth_1 }}
```

We can keep going like that for as long as we want. Running Z3 on SMT-LIB code enforcing this
methodology up to depth `2` produces the following output (see the [BMC with
Actlits](#bmc-with-actlits) section below for the full code).

```text
{{ #include code/sw_actlit_1.smt2.out }}
```

Pretty nice 😸. Let's never do this again manually to preserve our own sanity, and move on to the
next chapter where we will introduce mikino to do all of this automatically.


### Full Code For All Examples

#### Version 1

<details>
	<summary>Expand this for the full code.</summary>

```text
{{ #include code/sw_init_1.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_init_1.smt2.out }}
```
</details>

#### Version 2

<details>
	<summary>Expand this for the full code.</summary>

```text
{{ #include code/sw_init_2.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_init_2.smt2.out }}
```
</details>

#### BMC with Unrolling

<details>
	<summary>Expand this for the full code.</summary>

```text
{{ #include code/sw_init_3.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_init_3.smt2.out }}
```
</details>

#### BMC with Actlits

<details>
	<summary>Expand this for the full code.</summary>

```text
{{ #include code/sw_actlit_1.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_actlit_1.smt2.out }}
```
</details>


[TLA+]: https://lamport.azurewebsites.net/tla/tla.html (TLA+ website)