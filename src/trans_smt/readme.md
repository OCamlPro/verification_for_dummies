# SMT and Transition Systems

Time to use Z3 again: let's try to `assert` our transition relation so that we can use Z3 to answer
questions about the system. To do this, we need to write our transition relation in [SMT-LIB 2][smt
lib].

\
\

There's two new aspects of [SMT-LIB 2][smt lib] that will make things easier for us. First, SMT-LIB
identifiers can be *quoted* which means they can have form `|...|` where `...` is a sequence of
pretty much any character but `|`. This is convenient as it allows us to write, for example,
identifiers such as `|s'.is_counting|`. This will make things more readable, hopefully.

Second, [SMT-LIB 2][smt lib] allows us to *define functions* using the `define-fun` command. Its
shape is

```text
(define-fun <ident> ( <args> ) <type>
	<expression>
)
```

where `<args>` is zero or more arguments `(<ident> <type>)`. For example:

```text
{{ #include code/def_fun_demo.smt2 }}
```

Running Z3, we obtain

```text
> z3 test.smt2
{{ #include code/def_fun_demo.smt2.out }}
```

\
\

So, let's define a function for our transition relation. The definition is a bit daunting because,
again, [SMT-LIB 2][smt lib] is really designed to be parsed by solvers. Human readability is not
the main concern, but relatively small examples are quite readable if indented properly.

```text
{{ #include code/sw_trans_1.smt2:trans_def }}
```

> Full code in the [Version 1](#version-1) section below.

\
\

Now, if we want to use this transition relation function, we need to give ourselves actual state
variables to apply it to. Let's switch notation to prepare for the more complex manipulations we
will soon investigate. Let's distinguish state variables using indices: instead of referring to `s`
and `s'` to distinguish between *previous* and *next* state, let's just say we have a state of
index `0` and another one of index `1`. So, instead of writing `s.cnt` and `s'.cnt` we can just
write `cnt_0` and `cnt_1` respectively.

```text
{{ #include code/sw_trans_1.smt2:states_def }}
```

We can now `assert` our `trans`ition relation over these two states, *i.e.* force state `1` to be a
successor of state `0`.

```text
{{ #include code/sw_trans_1.smt2:unroll_1 }}
```

Nice 😸. Let's see if we can force state `0` and the inputs of state `1` to have Z3 produce a new
state that's a successor of state `0`. For instance,

- state `0`: `cnt` is strictly greater than `7` and `is_counting` is `false`;
- state `1`: `start_stop` is pressed and `reset` is not.

```text
{{ #include code/sw_trans_1.smt2:state_constraints }}
```

\
\

The `check-sat` command asks Z3 whether there exists a valuation of all state variables verifying
all our constraints. Said constraints include that state `1` must be a legal successor of state `0`.

> Full code in the [Version 1](#version-1) section below.

```text
> z3 test.smt2
{{ #include code/sw_trans_1.smt2.out }}
```

It works. In this *model* (yours might differ), Z3 decided to have `cnt_0` be `8` which, given all
the constraints, means that `cnt_1` is `9`. This is because `is_counting_1` is `true`, which is a
consequence of the last assertion we wrote (`is_counting_0` is `false` and `start_stop_1` is
`true`).

\
\

Maybe we can ask for something more interesting, *i.e.* maybe we can actually **prove** something.
Let's modify our last assertion: we keep the constraints over state `0` and replace state `1`'s by
`cnt_1` must be `0`.

```text
{{ #include code/sw_trans_2.smt2:state_constraints }}
```

> Note that this assertion **replaces** the one above where we constrained state `1`'s
> inputs.

The question we are asking Z3 is now *"say `cnt > 7` and we're not counting; is it possible then to
have `cnt = 0` in one transition?"*.

> Full code in the [Version 2](#version-2) section below.

```text
{{ #include code/sw_trans_2.smt2.out }}
```

Z3 answers *"yes"* (`sat`), and shows us that by pressing `reset` in state `1`, then we have `cnt =
0`. That's fair, but what if we don't allow `reset` to be pressed in state `1`?

```text
{{ #include code/sw_trans_3.smt2:state_constraints }}
```

Readers comfortable with our toy stopwatch system know this should not be possible. If `reset` is
not pressed, `cnt` can only increase or stay the same depending on whether the system is counting.

Humans (us) *"knowing"* this is not possible is not very valuable, as humans are notoriously great
at being wrong. Let's just ask Z3 to prove (or disprove) what we *know*.

> Full code in the [Version 1](#version-1) section below.

```text
> z3 test.smt2
{{ #include code/sw_trans_3.smt2.out }}
```

So, Z3's answer is that *"there exists no valuation of the state variables verifying these
constraints"*. That is, given the constraints on state `0`, it is not possible to reach a state
where `cnt = 0` and `reset` is not pressed in one transition.

\
\

We can see this result as a consequence of a more abstract *property* of the system. That is, there
are only three possible `cnt` values in the successor of any given state. Given `cnt_0`, `cnt_1`
can only be `0`, `cnt_0`, or `cnt_0 + 1`.

**Exercise**: have Z3 prove this property by rewriting the last assertion of [Version
3](#version-3). Check out [Version 4](#version-4) for the solution. **Hint below.**

<details>
	<summary>Hint.</summary>

Another way to look at what we want to prove is to say *"it is not possible for `cnt_1` to be
anything else than `0`, `cnt_0`, or `cnt_0 + 1`"*.

So, if we ask Z3 for a model where `cnt_1` is none of these and the answer is `unsat`, then we
would prove that `cnt_1` cannot be anything but one of these three (not necessarily distinct)
values.
</details>

\
\

### Full Code For All Examples

#### Version 1

<details>
	<summary>Expand this for the full code.</summary>

```text
{{ #include code/sw_trans_1.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_trans_1.smt2.out }}
```
</details>

#### Version 2

<details>
	<summary>Expand this for the full code.</summary>

```text
{{ #include code/sw_trans_2.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_trans_2.smt2.out }}
```
</details>

#### Version 3

<details>
	<summary>Expand this for the full code.</summary>

```text
{{ #include code/sw_trans_3.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_trans_3.smt2.out }}
```
</details>

#### Version 4

<details>
	<summary>Expand this for the full code.</summary>

```text
{{ #include code/sw_trans_4.smt2:all }}
```

Output:

```text
> z3 test.smt2
{{ #include code/sw_trans_4.smt2.out }}
```
</details>


[smt lib]: http://smtlib.cs.uiowa.edu (SMT-LIB homepage)