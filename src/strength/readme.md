# Candidate Strengthening

> Candidate strengthening is about making non-inductive candidates inductive (when possible). It is
> somewhat difficult to come up with an example that is
> - interesting for strengthening,
> - not too artificial, *i.e.* is relatively realistic for a developer, and
> - is accessible without too much explanation.
>
> While not extremely complex, the central example of this chapter and the manipulations in general
> are going to be more involved than what we have discussed so far.
>
> This chapter also touches on the very high complexity and potential undecidability of
> verification.
>
> This chapter is quite technical, and a bit theoretical. It is recommended that you understand all
> the concepts introduced so far before diving into this chapter. Some understanding of Rust could
> help in places, although it is by no means mandatory.

\
\

We have seen two kinds of candidate up to this point:

- inductive candidates, meaning induction can prove they are invariants, and
- falsifiable candidates, which can be falsified by running BMC for long enough.

Not all invariants are inductive. Meaning it is possible to get a *step* counterexample, *i.e.* the
transition relation does not preserve the candidate, even though the candidate is an invariant and
no legal trace of states can falsify it.

\
\


## Array Value Grouping

Let's switch gears and look at an actual piece of (Rust) code. Assume we have an array `arr` of
statically-known size `len` of elements of type `T` (`arr` has type `[T; len]`. Say we also have an
integer (`usize`) value `grouping`. What we want to do is [fold] over successive groups
(sub-arrays) of length `grouping` of the elements of `arr`.

In practice, we want to have a type `Wrap` that stores `arr` and `grouping`, and exposes a `fold`
function over values of type `&[T]` which is **guaranteed** to store exactly `grouping` elements.
Fold implements an sliding, non-overlapping window of length `grouping` over `arr`. Here is what
using it would look like.

```rust ,compile_fail,no_run
{{ #include code/split_0.rs:main }}
```

Which produces

```text
{{ #include code/split_0.rs.out }}
```

\
\


Full code available below. For now let's turn to how the `fold` function would be implemented. Say
`init` and `next` are `fold`'s two arguments (initial value and fold function respectively). Then
the body of `fold` could look something like

```rust ,compile_fail,no_run
{{ #include code/split_0.rs:fold_body }}
```

- local variable `acc` is initially `init`, and the loop updates its value with the result of the
  call to `next`;
- the `while` loop increments an `i` index until it goes over `len` (length of `arr`);
- at the end of each iteration, the new value of `i` is `i + grouping`;
- the call to `next` gives it the current value of the accumulator, and a slice from `i` to `i +
  grouping` ---remember that `n..m` is the interval `[n, m[`: `m` is not included in the interval;
- when we exit the loop, we return the final value of `acc`.

<details>
	<summary>Full code for this example, requires some Rust knowledge.</summary>

```rust
{{ #include code/split_0.rs:all }}
```
</details>

\
\

Now let's think about this a little bit. The value `&arr[i..next_i]`, where `next_i` is `i +
grouping`, does not always *make sense*: `i + grouping` might strictly superior to `len` (`arr`'s
length). This cannot happen if `len` is a multiple of `grouping` however, and actually `Wrap`'s
constructor checks for this.

```rust ,compile_fail,no_run
{{ #include code/split_0.rs:constructor_check }}
```

There is also a check that `grouping > 0`, otherwise `fold` would not terminate when `len > 0`. So
everything should be fine, right? Humans do not make very good proof engines, let's just prove it
to make sure.

\
\


## Encoding

> You are encouraged to think about how you would encode this verification problem so that mikino
> can handle it. You will probably not going to succeed unless you are already very familiar with
> this kind of encoding. May read a paragraph below or two, think about it some more, read some
> more, *etc.*

Mikino does not accept Rust code, we need to encode what we want to check. Writing an encoder for
(a subset of) of programming language is a very challenging task. It requires an exact
understanding of the semantics of the language and the ability to design encoding rules that
*are guaranteed* to preserve it, or at least preserve the part relevant for the analysis.
So let's not do that and encode it by hand.

```rust ,compile_fail,no_run
{{ #include code/split_0.rs:fold_body }}
```

What do we want to check, *i.e.* what does it mean for this code to *make sense*? It's really a
matter of how `i` is related to `len`. Each iteration *makes sense* if the interval we use on `arr`
is legal, meaning `i < len` and `next_i = i + grouping ≤ len` (interval is exclusive on its upper
bound). We actually don't care about what's in `arr`, just that its length is `len`. Our encoding
can safely ignore `arr` completely. Same for `acc`, its value is not relevant for `fold` to make
sense in how it accesses `arr`. The only real state variable of interest in this loop is thus `i`.

> There a whole bunch of additional properties we might want to prove. For instance, that `arr`
> slices do not overlap. The point is that, whatever we are interested in proving, we should remove
> everything that is not necessary as we encode the program. However, the encoding should at least
> be *sound*: proving an invariant in the encoding must entail it is an invariant for the original
> program.
>
> Here, we are doing the encoding by hand and we can pick and choose what is encoded or left out.
> In an actual verification tool, the encoding process would be automatic. Such an automatic
> encoder might encode the whole semantics of the program (meaning dealing with arrays at SMT-level
> here) and hope for the best, or be clever enough to realize it can excise array-related things
> for this particular verification challenge. Writing a clever, automatic encoder is difficult and
> challenging, and can void all results if it is not *sound*.

\
\

Note that we have a few constants here: `len` and `grouping` do not change as the loop runs.
Unfortunately mikino does not have a notion of constant **yet** (contributions are welcome), so we
have to encode them as state variables along with `i`.

```rust ,compile_fail,no_run
{{ #include code/split_cex_0.mkn:vars }}
```

The surprise state variable `done` is a flag we are going to use to indicate whether the loop is
done or not. This allows our system to never end, which is a useful property for technical reasons
beyond the scope of this chapter.

We initialize the transition system encoding `fold`'s loop, as follows.

```rust ,compile_fail,no_run
{{ #include code/split_cex_0.mkn:init }}
```

The first two simply constrain the values for `len` (`usize`, thus `≥ 0`) and `grouping` (checked
to be `≥ 1` by the constructor). Then `i` is constrained to be equal to its initial value, `0`. The
`done` flag is initially true if and only if `i ≥ len`, which basically means `len` is `0` ---`arr`
is empty, the loop never starts.

Last, we have the assumption we need for the whole thing to work: `len` is a multiple of
`grouping`, which `Wrap`'s constructor checks.

\
\

The transition relation needs to do a few things. Our constants (encoded as state variables) need
to keep their value, since if we left them unconstrained they could take any value. We also need to
update the value of `done`, and finally that of `i`.

```rust ,compile_fail,no_run
{{ #include code/split_cex_0.mkn:trans }}
```

\
\


## Testing the Encoding

Before we do anything else, let's think of what happens if `len = 8` and `grouping = 4`. Initially
`i = 0`, then it should increase to `i = 4`, then to `i = 8` at which point `done = i ≥ len`
becomes `true` and the system stutters (its state variables stay the same forever).

We should make sure our encoding behaves like this. So, what we should ask mikino is *"with `len =
8` and `grouping = 4`, is it possible to reach a state such that `i = len`?"*. We can do this with
BMC: since we want to reach `len = 8 ∧ grouping = 4 ∧ i = len`, we can just need ask BMC to try to
falsify `¬(len = 8 ∧ grouping = 4 ∧ i = len)`.

```rust ,compile_fail,no_run
{{ #include code/split_cex_0.mkn:candidates }}
```

Mikino yields

```text
> mikino bmc test.mkn
{{ #include code/split_cex_0.mkn.out }}
```

We got exactly what we expected, that's encouraging. Also, remember that [we proved that BMC
produces counterexamples of minimal length][bmc short]. Hence, no shorter trace of states can lead
the system to falsify our property.

Full code available in the [Version 1](#version-1) section. You are encouraged to mess around with
the example to get a better understanding of the encoding.

> Mikino reports that Z3 produced unexpected values. This is not relevant for our discussion, but
> these *functions* are part of the model. Z3 is letting us know how it decided to handle division
> (modulo) by `0`. I won't go into deeper details here for space constraints, but this is a
> consequence of the fact that our system uses *non-linear arithmetic*, and non-linear division in
> particular. A (system made of) formula(s) *uses non-linear arithmetic* if it uses
> multiplication/division involving more than one variable (`x * y`, `x / y`). As opposed to
> *linear arithmetic* which only allows one variable to be used (`3 * x`, `x / 7`, `0 / x`).
>
> SMT is *not decidable* when non-linear arithmetic is involved, but we will have more to say on
> that shortly as we will run into this exact problem.

\
\

## Diving Head First

We start with trying to prove that the lower bound of the interval `i..(i + grouping)` used on
`arr` is legal, meaning to prove that `i < len`. More precisely, `¬done ⇒ i < len` since on exit
(when `done` is `true`) we actually should have `i = len`; let's prove `done ⇒ i = len` as well.

```rust ,compile_fail,no_run
{{ #include code/split_0_0.mkn:candidates }}
```

Full code in the [Version 2](#version-2) section. Running mikino in `check` mode, we get:

```text
> mikino check test.mkn
{{ #include code/split_0_0.mkn.out }}
```

Well, the good news is that the lower bound of our interval is always legal: mikino proved it. We
get a counterexample (cex) for the second candidate though. A stupid cex too, as `i` is *obviously*
positive. At least, it is obviously positive if you take into account the initial states (`i` = 0),
which the *step* check of the induction proof does not do by definition. As far as the transition
relation is concerned, there is no reason for `i` to be positive at some step `k`.

\
\

Your first reflex might be to add this constraint to the transition relation (`(pre i) ≥ 0`), which
is a terrible idea. That's the encoding of the original code, you should not touch it as this would
actively mask cex-s. Spurious cex-s in this case, but if you make any mistake when augmenting
`trans` then you might block actual cex-s and safety proofs you might get would not say anything
about the original system.

The reason why, in this case, it **would** be safe to add `(pre i) ≥ 0` (don't do it though) is
that it is an invariant, *i.e.* a *consequence* of the system's behavior. So there's no reason to
force it on `trans`, we can just ask mikino to prove it instead.

```rust ,compile_fail,no_run
{{ #include code/split_0_1.mkn:candidates }}
```

Full code in the [Version 3](#version-2) section. Mikino tells us

```text
> mikino check test.mkn
{{ #include code/split_0_1.mkn.out }}
```

\
\

Okay, now `grouping` is negative. There is a pattern emerging: mikino (*induction*, really) is
stupid and needs to be told everything.

\
\


## Strengthening 💪

When we add `i ≥ 0` as a candidate, we are *strengthening* candidate `done ⇒ i = len`. That is,
this candidate is *not* inductive on the *raw system* (made of `init` and `trans`). If we hope to
prove it by induction, we have to try to prove a *stronger* version `(done ⇒ i = len) ∧ lemma`, for
example with `lemma ≝ i ≥ 0` in the previous example. We added the lemma as a separate candidate,
but morally `lemma` was not really what we wanted to prove, it was just a *lemma* we added to help
prove the main candidate (which failed). It did not work, but if we can find a `lemma` for which
the proof goes through, then we won since the fact that `(done ⇒ i = len) ∧ lemma` is an invariant
implies that `done ⇒ i = len` is an invariant.

> We are about to strengthen this candidate manually, but maybe you can see why many
> induction-based proof engine have some form of *invariant discovery*. Such techniques aim at
> discovering potentially complex lemmas about the system that strengthen the candidates when
> they are not inductive.

\
\


We could keep on asking mikino for *step* cex-s and come up with a candidate that will hopefully
block them. But we have been doing this whole thing wrong.

The first thing we should do is write everything we expect to be an invariant. For instance we know
that `len ≥ 0`, and that `grouping ≥ 1` and `len % grouping = 0` (both checked in the constructor).
Our first move should have been to write these candidates down (in addition to `i ≥ 0`) and make
sure they are actually (inductive) invariants. Besides hopefully strengthening our original
candidates (`done ⇒ i = len` and `¬done ⇒ i < len`), we must check that they are invariants since
if they are not something is very wrong ---the system, our encoding, our overall understanding, or
all of the above.

Note that, if the encoding process was automatic, these candidates could have been generated
automatically: `len: usize` implies `len ≥ 0`, same for `i`, and the checks in the constructor
guarantee `grouping ≥ 1` and `len % grouping = 0` since neither `len` nor `grouping` ever change.
As we will see, this is not enough, and we will need to add another (candidate) invariant that is
less trivial to strengthen our real candidate successfully.

\
\

For now let's just add these new candidates

```rust ,compile_fail,no_run
{{ #include code/split_0.mkn:candidates }}
```

and run mikino. Full code in the [Version 4](#version-4) section.

```text
> mikino check test.mkn
{{ #include code/split_0.mkn.out }}
```

At least the new candidates are actual (inductive) invariants. It was not enough to strengthen our
real candidate, but the cex we got is interesting. With `len = 4` and `grouping = 2`, the step
check is able to go from `i = 3` to `i = 5` and falsify the main candidate.

The problem here, as you might have guessed, is currently `i` can really take any value as long as
its positive: no (candidate) invariant constrain it besides `i ≥ 0`. Looking at the code for the
loop again

```rust ,compile_fail,no_run
{{ #include code/split_0.rs:fold_body }}
```

we see that `i` can only be a multiple of `grouping`. But we cannot know until we try to prove it.
Also, will it strengthen our main candidate enough to make it inductive?


```rust ,compile_fail,no_run
{{ #include code/split_1.mkn:candidates }}
```

We run mikino but, inconspicuously, we change the command used to run Z3 slightly (change `z3` in
the string to whatever the path to your Z3 binary is). Full code in the [Version 5](#version-5)
section.

```bash
> mikino --z3_cmd "z3 -T:5" check test.mkn
{{ #include code/split_1.mkn.out  }}
```

Adding `-T:5` to the Z3 command tells Z3 to timeout after five seconds. Feel free to increase the
timeout, unless you are from the future and using a version Z3 that performs better on non-linear
arithmetic, the *step* check will never end. Because of...


\
\


## Undecidability

This small aside illustrates the importance of delimiting precisely the *logical fragment* in which
your encoding takes place. That is, what the formulas mention: strings, arrays, non-linear
arithmetic?

Verification is expensive; very expensive. SMT checks themselves are at least exp-time, meaning
that if `n` is *"the size of the problem"*, the complexity of SMT checks is at least `2ⁿ`. Most
SMT-based verification techniques end up being at least `k`-exp-time, also informally called *tower
of exponential*, which is even worse than it sounds:

```text
2^(2^(2^(2^(.....2ⁿ))))
^^^^^^^^^^^^^^^^^^
    `k` times
```

where `k` is some arbitrarily large constant specific to a given problem.

So that's not great. As it turns out, the hardware is now so efficient and the tools so carefully
implemented and optimized that despite being `k`-exp-time, we can actually verify very interesting
and complex systems. Still, given the complexity, we can only go so far.

One way around this high complexity is to analyze complex systems *compositionally*, which is akin
to type-checking. When proving function `f`, which calls `g`, we can abstract `g` away if we have
some specification for it, effectively replacing `g`'s implementation by what the specification
says it does. Then we prove `g` respects its specification, recursively.

This assumes we have a specification for sub-functions (`g`), and not just a single specification
at the top-most level (`f`). *Refining* a top-level specification to generate specifications for
the sub-functions is very difficult to do automatically (also *manually*).

\
\

To sum up, verification has at best a very high complexity. Still, in theory, if you had enough
time and memory you could just wait for an arbitrary long time and actually get an answer. Unless
you are in an *undecidable* logic fragment: you cannot know in advance if you will get an answer,
even if you wait for an infinite amount of time and memory.

That's not great either, and in fact this is (probably) what happened to us on

```rust ,compile_fail,no_run
{{ #include code/split_1.mkn:candidates }}
```

when we got

```bash
> mikino --z3_cmd "z3 -T:5" check test.mkn
{{ #include code/split_1.mkn.out  }}
```

We have been in an undecidable fragment all along (since we use non-linear arithmetic). But so far,
we managed to only send Z3 checks it could handle. The last candidate we added, `i % grouping = 0`,
apparently made our checks escape Z3's abilities.

And that's pretty much it, we will not prove `done ⇒ i = len` and probably not other interesting
properties such as *"the upper bound of the interval `i..(i + grouping)` must be `≤ len` (interval
exclusive on the upper bound)"* (or simply `i + grouping ≤ len`) either.

Or maybe what we could do is...

\
\


## Settling For The Next Best Thing

Our current system is very loose on what `len` and `grouping` could be. We cannot say much on
`grouping` as it is given to the code at runtime. It can be anything (module the constructor's
checks) and we have no control over it at compile-time (verification-time). But `len` is different.

It is actually not unknown at compile-time since it is a `const`, *i.e.* a value that can be
computed when compiling ---at least when compiling a binary using this code, but not necessarily
when compiling a library. See section [Rust System](#rust-system) for the full Rust code of the
system. More precisely, different version of our case-study might be used: with `len = 3`, `len =
7`... But the point is that, due to how Rust works (*monomorphization* in particular), there is a
finite number of actual `len` values and we know all of them. (Again, at least when compiling a
binary.)

\
\

So, maybe, instead the loose constraint `len ≥ 0` and trying to conduct a proof for any value of
`len` (which does not work, as we have seen), we could check each possible value of `len`
separately. Notice that `len` is used in a non-linear `mod` application, `len % grouping`:

```rust ,compile_fail,no_run
{{ #include code/split_1.mkn:candidates }}
```

Checking for the concrete possible values of `len` instead would remove this non-linear `mod` and,
maybe, simplify our checks enough that Z3 can handle them. Let's try with `len = 8`; we could
remove the `len` state variable altogether, but we can try simply forcing it to be `8`. To do this,
first we need to change `init` slightly:

```rust ,compile_fail,no_run
{{ #include code/split_2.mkn:init }}
```

Nothing to do on `trans`, it does not mention `len` anyway. The candidate `len ≥ 0` changes to
become more precise though:

```rust ,compile_fail,no_run
{{ #include code/split_2.mkn:candidates }}
```

While we still have the non-linear `len % grouping`, the (candidate) invariant `len = 8` might
actually be enough for Z3 to handle the checks on this system. We shall see.

Full code in the [Version 6](#version-6) section. Crossing our fingers, we nervously run mikino:

```text
> mikino --z3_cmd "z3 -T:5" check test.mkn
{{ #include code/split_2.mkn.out }}
```

🎊 🎉 👏 🎊

\
\


## Wrapping Up

We proved the lower bound of the interval in `&arr[i..(i + grouping)]` is legal 🎉. But that's not
enough for the program to be safe, since we have not proved that the upper bound is legal. That is,
prove that `i + grouping ≤ len` (interval *still exclusive* on the upper bound 😔).

By now you might be familiar enough with induction's *step* checks to be able to anticipate whether
this candidate is going to be inductive or not.

```rust ,compile_fail,no_run
{{ #include code/split_3.mkn:candidates }}
```

Full code in the [Version 7](#version-7) section.

🥁🥁🥁🥁🥁🥁

```text
> mikino --z3_cmd "z3 -T:5" check test.mkn
{{ #include code/split_3.mkn.out }}
```

🎉

\
\

It might be disappointing that we had to choose a value for the length, *i.e.* that we did not
prove that `fold`'s array accesses are legal when `len` is `8`. Unfortunately, in its current
state, Z3 cannot handle to have `len` as an unknown value because of the non-linear applications of
modulo.

This means that, assuming we are verifying a binary, we can conduct the same proof for all `len`
values actually used by the program. It would be much better to verify `fold` for any length, but
this illustrates the kind of trade-offs that are often necessary in a verification process due to
the very high complexity (and sometimes undecidability) of the checks intrinsic to the verification
approach.

\
\

## Full Code for All Examples

### Rust System

<details>
	<summary>Expand this for the full code.</summary>

```rust
{{ #include code/split_0.rs:all }}
```

Output:

```text
{{ #include code/split_0.rs.out }}
```
</details>


### Version 1

<details>
	<summary>Expand this for the full code.</summary>

```rust ,compile_fail,no_run
{{ #include code/split_cex_0.mkn:all }}
```

Output:

```text
> mikino check test.mkn
{{ #include code/split_cex_0.mkn.out }}
```
</details>

### Version 2

<details>
	<summary>Expand this for the full code.</summary>

```rust ,compile_fail,no_run
{{ #include code/split_0_0.mkn:all }}
```

Output:

```text
> mikino check test.mkn
{{ #include code/split_0_0.mkn.out }}
```
</details>

### Version 3

<details>
	<summary>Expand this for the full code.</summary>

```rust ,compile_fail,no_run
{{ #include code/split_0_1.mkn:all }}
```

Output:

```text
> mikino check test.mkn
{{ #include code/split_0_1.mkn.out }}
```
</details>

### Version 4

<details>
	<summary>Expand this for the full code.</summary>

```rust ,compile_fail,no_run
{{ #include code/split_0.mkn:all }}
```

Output:

```text
> mikino check test.mkn
{{ #include code/split_0.mkn.out }}
```
</details>

### Version 5

<details>
	<summary>Expand this for the full code.</summary>

```rust ,compile_fail,no_run
{{ #include code/split_1.mkn:all }}
```

Output:

```text
> mikino --z3_cmd "z3 -T:5" check test.mkn
{{ #include code/split_1.mkn.out }}
```
</details>

### Version 6

<details>
	<summary>Expand this for the full code.</summary>

```rust ,compile_fail,no_run
{{ #include code/split_2.mkn:all }}
```

Output:

```text
> mikino check test.mkn
{{ #include code/split_2.mkn.out }}
```
</details>

### Version 7

<details>
	<summary>Expand this for the full code.</summary>

```rust ,compile_fail,no_run
{{ #include code/split_3.mkn:all }}
```

Output:

```text
> mikino check test.mkn
{{ #include code/split_3.mkn.out }}
```
</details>



[fold]: https://en.wikipedia.org/wiki/Fold_(higher-order_function)
(The fold function on wikipedia)
[bmc short]: ../induction (Induction chapter)