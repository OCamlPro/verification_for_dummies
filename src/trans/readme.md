# Transition Systems

> This chapter is a bit abstract, there will be no fun manipulations 😿. The next chapter builds on
> this one and is nothing but fun manipulations 😺 on the notions and examples introduced here.
> Transition systems are the *"objects"* we will later analyze and are, in a sense, relatively
> close to pieces of actual code (loops). This chapter starts bridging the gap between the
> relatively high-level notion of transition system and SMT solvers which are relatively low-level
> tools.

\
\

A *(declarative) transition system* describes an infinite loop updating some *state*. The *state*
can be understood as some variables storing some data. These variables are usually called *state
variables* and they characterize the system completely. At each *step*, or *iteration of the loop*,
the state is updated (the state can change). A loop, even an infinite loop, has to start somewhere.
It may have more than one way to start itself: the *initial states* encapsulate all the different
ways the loop can start.

\
\

Say we have a simple stopwatch system. It features a `start_stop` button (toggles counting) and a
`reset` button. Say also this system counts time as an integer `cnt`. While `start_stop` and
`reset` are inputs (users control whether they are pressed or not), `cnt` corresponds to the
stopwatch's display: it is an output.

We also need an internal variable `is_counting` to remember whether we are counting or not:
`start_stop` toggles counting, meaning we need to remember if we were previously counting or not to
decide what a press of the `start_stop` button does. Hence, the state variables (`svars`) of our
stopwatch are

```rust ,no_run,compile_fail
svars {
	// inputs, `true` if pressed
	start_stop reset: bool,
	// internal variable
	is_counting: bool,
	// output
	cnt: int,
}
```

> As we will see later, this is the actual syntax we will use once we start playing with the mikino
> induction-based checker.

The description of this system is

- the system is initially not counting;
- when not counting, a press on `start_stop` switch to counting mode (and conversely);
- a press on `reset` resets the counter to `0`;
- when counting and not resetting, `cnt` keeps incrementing.

<details>
	<summary>Expand this for a runnable implementation in Rust.</summary>

```rust ,editable
{{ #include code/sw_1.rs }}
```

</details>

\
\

## Initial Predicate

Let us think in terms of constraints: what must the values of the state variables verify to be a
legal initial state? We only have one constraint, `reset => cnt = 0`. That is, if `reset` is
`true`, then `cnt` must be `0`, otherwise anything goes. Given the description of the system, this
constraint captures the legal initial states and only the legal initial states.

This is called the *init predicate* of the transition system. The init predicate takes a state
valuation as input, and is true if and only if that state valuation is a legal initial state. We
can write it in pseudo-code as `init(s) ≜ s.reset ⇒ s.cnt = 0` or, equivalently, `init(s) ≜
¬s.reset ∨ (s.cnt = 0)`: *"either `reset` is `false` or `cnt` is `0`"*.

> It might seem like a detail, but you should **not** think of `s.cnt = 0` as an assignment. It is
> really a constraint that evaluates to `true` or `false` depending on the value of `s.cnt`. If it
> helps, you can think of `=` as the usual `==` operator found in most programming languages.

Our initial predicate is not complete though. The specification also tells us that we are
originally *not counting*, and that when `start_stop` is `true` we should toggle counting on/off.
That is, the initial value of `is_counting` should be `false` when `start_stop` is `false` (not
pressed), and `true` when `start_stop` is `true` (pressed). Hence, the initial value of
`is_counting` is `start_stop`. Our initial predicate is thus

```text
init(s) ≜ (s.reset ⇒ s.cnt = 0) ∧ (s.is_counting = s.start_stop)
```

\
\

## Transition Relation

So at this point we have a notion of state (data) maintained by the transition system, and a
predicate (formula) that is true on a state valuation if and only if it is a legal initial state.
We are only missing the description of how the system evolves.

This is what the *transition relation* (a.k.a *step relation*) does. Its job is to examine the
relation between two state valuations `s` and `'s`, and evaluate to `true` if and only `'s` is a
legal successor of `s`. The first part of the *transition relation* deals with `is_counting`, which
should be toggled by `start_stop`. This is a constraint, if `'s` is a successor of `s` then they
should verify

- `'s.start_stop ⇒ ('s.is_counting = ¬s.is_counting)`, and
- `¬'s.start_stop ⇒ ('s.is_counting = s.is_counting)`.


Note that we still have a constraint when `start_stop` is not pressed: the value should not change.
If we did not constrain `'s.is_counting` in this case, then it would be unconstrained and thus
could take any value. These two constraints are arguable more readable as

- `'s.is_counting = if 's.start_stop { ¬s.is_counting } else { s.is_counting }`.

\
\

Next, the system's description discusses how `cnt` evolves, which gives the following constraints:

- `'s.reset ⇒ ('s.cnt = 0)`,
- `'s.is_counting ⇒ ('s.cnt = s.cnt + 1)`, and
- `¬'s.is_counting ⇒ ('s.cnt = s.cnt)`.

Most readers might notice that these constraints will not work well together. Whenever `reset` is
pressed `cnt` must be `0`, and at the same time it must be either incremented or unchanged
depending on the value of `is_counting`. In most cases, these constraints will have no solution.

<details>
	<summary>Expand this for a concrete example of a conflict.</summary>

> Say `s.cnt = 1`, and both `'s.reset` and `'s.is_counting` are `true`. Then by the first
> constraint, we must have `'s.cnt = 0`; by the second constraint, we must also have `'s.cnt = 2`.
> Hence, both constraints are in conflict and, together, they are unsatisfiable.

</details>

Assuming the order of the points in the description of the system matters, we can solve this problem
by making the `reset` behavior preempt the behavior related to `is_counting`. We get

- `'s.reset ⇒ ('s.cnt = 0)`,
- `('s.is_counting ∧ ¬'s.reset) ⇒ ('s.cnt = s.cnt + 1)`, and
- `(¬'s.is_counting ∧ ¬'s.reset) ⇒ ('s.cnt = s.cnt)`.

Alternatively, we can rewrite these constraints as

```rust ,compile_fail,no_run
's.cnt =
	if 's.reset { 0 }
	else if 's.is_counting { s.cnt + 1 }
	else { s.cnt }
```

Our transition relation is thus

```rust ,compile_fail,no_run
trans(s, 's) =
	  ( 's.start_stop ⇒ ('s.is_counting = ¬s.is_counting))
	∧ (¬'s.start_stop ⇒ ('s.is_counting =  s.is_counting))
	∧ (
		's.cnt =
			if 's.reset { 0 }
			else if 's.is_counting { s.cnt + 1 }
			else { s.cnt }
	)
```

\
\

Notice that `trans` only really constrains `'s.is_counting` and `'s.cnt`. This makes sense as the
two other states variables `'s.start_stop` and `'s.reset` (both of type `bool`) are seen as
*inputs*. Since they are not constrained, they can take any (boolean) value at all.

Notice also that, if we fix some values for `'s.start_stop` and `'s.reset`, then `trans` is
*deterministic*: `s`, whatever it is, can only have one successor.

| `'s.start_stop` | `'s.reset` | `'s.is_counting` | `'s.cnt` |
|:---:|:---:|:---:|:---:|
| `false` | `false` | `s.is_counting` | `if 's.is_counting { s.cnt + 1 } else { s.cnt }` |
| `true` | `false` | `¬s.is_counting` | `if 's.is_counting { s.cnt + 1 } else { s.cnt }` |
| `false` | `true` | `s.is_counting` | `0` |
| `true` | `true` | `¬s.is_counting` | `0` |

So, there are **at most** four potential successors to any state `s`, depending on the
(unconstrained) values of the two inputs.
