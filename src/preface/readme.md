# Preface

> This preface is a high-level introduction to formal verification. It then goes into the details
> of what a formal verification tool looks like, and which aspects of such tools we will discuss in
> later posts.

\
\

[Formal logics][logics] deal with reasoning in the context of a formal framework. For example, a
*type system* is a formal framework. [Strongly-typed][strong typing] programming languages rely on
type systems to (dis)prove that programs are well-typed. For example, consider the following Rust
function.

```rust
fn demo(n: usize) -> usize {
    let mut res = n;
    if n % 2 == 0 {
        res = 2*n;
    } else {
        res = 2*n + 1;
    }
    return res;
}
println!("demo(7): {}", demo(7))
```

When the Rust compiler type-checks this function, it goes through its body and aggregates some
*constraints*. These constraints are an abstraction of the definition that the type system can
reason about to (dis)prove that the program respects some type-related properties. For instance,
`let mut res = n;` is abstracted as *"`res` has the same type as `n`"*. The fact that, at this
point, `res` is equal to `n` is not relevant for type-checking.

\
\

Rust's most peculiar feature is the notion of *ownership* and the associated
[*borrow-checker*][borrow checker]. Similar to type-checking, borrow-checking abstracts the actual
code to encode it in a framework so that it can reason about the program. Type-checking's core
notion is that of types, and the equivalent for borrow-checking is *lifetimes*, *i.e.* the length
of time for which some data exists and can be used.

> Understanding lifetimes and the borrow-checker is not required for the next chapters. It is
> presented here as an example of encoding a problem in a framework where constraints can be
> constructed. Looking at these constraints, a tool (the borrow-checker here) can draw conclusion
> regarding the (un)safety of the program.

Consider the following Rust function, where `'a` is a lifetime parameter.

```rust ,compile_fail
// DOES NOT COMPILE
fn demo<'a>(n: &'a mut usize) -> &'a mut usize {
    let mut res = *n;
    res += 1;
    // error[E0515]: cannot return reference to local variable `res`
    return &mut res;
    //     ^^^^^^^^ returns a reference to data owned by the current function
}
```

Now, this code does not compile because of the notion of *ownership*. Here, the function's body
*owns* `res` since it created (allocated) it and, since it does not transfer `res` itself to the
caller (only `&mut res`), `res` is freed when we exit the body of the function (`res`'s owner):

- *i)* `res` only lives for the lifetime `'demo` (lifetime of the body of `demo`)
- *ii)* `demo` returns a mutable reference to `res`
- *iii)* the output of `demo` is a mutable reference of the same lifetime `'a` as its input

The compiler can then infer that `demo`'s output has lifetime `'demo` from *i)* and *ii)*, and thus
`'a` must be equal to `'demo` from *iii)*. However, it follows from *iii)* that `'a` must, in
general, live strictly longer (be valid for longer) than `'demo`. So, we have `'a > 'demo` and
since `'a = 'demo`, we reach a contradiction: `'demo > 'demo`. This means that there is no solution
to the constraints, and the compiler proceeds to reject the program by telling us that `res` does
not live long enough.

\
\

Type-checking and borrow-checking are examples of verification processes. In both cases, the
semantics of the program is encoded in a proof system. The encoding of the program and the rules of
the proof system let the compiler build a set of *constraints*.

It is interesting to note that *formal verification*, at its core, really consists in **searching
for a proof** of correctness. As we saw, the borrow-checker aggregates constraints and then looks
for a solution. In the paragraph above, we were looking for an interpretation of the different
lifetimes of the program that verifies, or *"satisfies"* all the constraint.

\
\

Searching for a proof, which consists in trying to *solve* some constraints is done by a *solver*.
From our point of view, the solver is our main building block. It is the block responsible for producing an actual answer from the encoding of the verification problem.


Now, the real question is *"what does it mean for the constraints to have a solution, or to have
none?"*. In the case of type-checking, the type constraints have a solution *if and only if* the
program is well-typed. It says very little about memory-safety and thread-safety on its own, which
is why type-checking is followed by borrow-checking in the Rust compiler.

The borrow-checker on the other hand builds constraints such that the existence of a solution
implies the absence of **U**ndefined **B**ehavior (UB) in the program. At least as long as there
are no `unsafe` blocks in it.




## Properties and Specification

The main point of the discussion above is to highlight a well-known fact in formal verification.
There is no such thing as *verifying a program*: all we can do is verify that *some properties*
hold for a program. This might seem like a trivial distinction, but it has consequences that
verification novices tend to overlook.

Type-checking and borrow-checking verify *built-in* properties: the program is well-typed and
cannot exhibit UB. We do not need to write a *specification* to tell them to verify these
properties. (Arguably, the type/ownership information we write throughout the program acts as a
partial/local specification.)

\
\

As a consequence, if we want to verify something the compiler is not able to do, we need two
things. First, we need some kind of *specification*, *i.e.* the properties we want to prove. We
might want to prove relatively general properties, for instance that no division by zero can occur.
Similar to type-checking and borrow-checking, this kind of property is built-in: whatever the
program to verify is, the property stays the same.

But our properties might depend on the exact program that goes through the verification process.
For example, we might want to prove input/output *contracts* on the functions of the programs we
analyze: the output of `fun_1` is positive, the output of `fun_2` is strictly greater than its
second input... In this case, programs will need some kind of annotation to *specify* these
contracts. Contrary to built-in properties, these program-specific properties are an input of the
verification tool.



## Solvers and Encoding

The second thing we need is a solver in which we can reason about the properties we are interested
in, on the programs we are interested in. In general, the solver will not accept the programs we
want to solve directly: we need to perform some encoding to generate the constraints for the solver.

The endgame is to build a verification tool that looks something like this:

```text

                              ┌───────────────────────┐
                              │   Verification Tool   │
                              ├───────────────────────┤
 ┌─────────────────────┐      │                       │
 │   Program to check  │      │     ┌──────────┐      │
 │and properties if not├──────┼─────► Encoding │      │
 │      built-in       │      │     └────┬─────┘      │
 └─────────────────────┘      │          │constraints │
                              │          │            │
                              │      ┌───▼─────┐      │
                              │      │ Solving │      │
                              │      └───┬─────┘      │
                              │          │success     │
                              │          │or failure  │
 ┌──────────────────────┐     │  ┌───────▼─────────┐  │
 │ User-friendly output ◄─────┼──┤ Post-processing │  │
 └──────────────────────┘     │  └─────────────────┘  │
                              │                       │
                              └───────────────────────┘

```


### Expressiveness

An important thing we have to consider is the *expressiveness* of the solver: it must be able to
represent and reason about our programs well enough that it is able to check our properties.

**Spoiler alert**: verification is expensive. Usable, practical formal verification requires quite
a lot of clever engineering at every level. Also, generally speaking, the more expressive a solver
is the more expensive using it will be. Roughly speaking, ideally, a good/efficient solver for a
verification process is a solver that can handle exactly what we need and nothing else.

This is in fact how verification projects start, usually. Verification experts will take a very
long look at the kind of programs and properties targeted by the project and establish a list of
suitable solvers. Crucial aspects to look for in this process include

- **types** of the values manipulated: booleans, integers, floats, hash sets, lists, user-defined
  types...
- **operations** over these values: linear multiplication, non-linear multiplication, modulo...
- **control flow**: recursion, iterators, loops, pattern-matching, switch-case...

Delimiting some kind of *expressiveness perimeter* to describe what we want the solver to support
is crucial and quite technical. The immediate danger is to get this perimeter wrong, and later
realize that aspects we missed make the solver we selected useless. This is why it tends to be
difficult to extend the expressiveness of a verification framework in directions not identified in
early stages.

If, when we chose the solver, all we had were booleans and integers with the usual operations over
them, it is for example very unlikely that we will be able to handle hash sets without huge changes
in the verification framework such as changing the solver.


### Soundness (of the Encoding)

Solvers have a notion of *soundness*. Roughly, a solver is *sound* if it can only prove *valid*
results (meaning it cannot prove things that are *"wrong"*). Since we are interested in *using*
(not *designing*) solvers, let's not go into more details on the notion of solver soundness and
only consider sound solvers.

\
\

There is a second notion of *soundness* however, which concerns the *encoding*. The *encoding* is
the process of going from an input program (and specification) to whatever kind of system the
solver can work on. This step will typically abstract the semantics of the program, as generally
speaking we cannot represent its exact semantics in the solver's input language.

The process of encoding is *sound* if whenever we prove that the encoded program verifies some
property `Prop`, then necessarily the original program verifies `Prop` as well. In case it is not
clear, if the goal is formal verification then **we need the encoding to be sound**. Otherwise, a
proof on the encoded program tells us nothing of the real program, *i.e.* the one we want to verify
in the first place.

> This is not to say that unsound encodings are necessarily useless. They can be useful if we are
> interested solely in finding bugs for instance. Since we will not try to prove anything, it is
> fine for the encoding to be unsound as long as it allows us to find actual/potential bugs.


## Outro

I hope I got across the point that setting up a verification process in a (semi-)industrial context
requires a great deal of inspection. It requires assessing very precisely what kind of program we
want to analyze, and what kind of property we want to check. Widening the perimeter of
programs/properties supported can be arbitrarily complex.

\
\

Another important point is that the actual verification framework should be written very carefully.
While the solver is usually very trustworthy, any issue in the steps between the input program and
specification and the solving (parsing, pre-processing and encoding) potentially voids any
successful proof attempt. The solver **must** work on a correct encoding of the problem for the
result to mean anything.

Note that the problem is less severe for failed proof attempts that produce a *counterexample* (an
*executable* witness of a falsification of the property). Checking that the counterexample makes
sense for the original program is easy and fast. But a proof of correctness relies on the encoding
being sound and correctly implemented.

> There are ways to mitigate this kind of problem. Soundness can be formally proved. The frontend
> can be made redundant by implementing it twice by two different teams in two different languages
> (two or more), and checking they produce exactly the same constraints. Solver-side, *proof
> logging* consists in having the solver log the logical steps of the actual proof it found so that
> they can be checked by one or more separate tools.


## Next

The following posts dive into SMT-based transition system induction, with some property
strengthening at the end. We will first get to know *SMT solvers*, which are powerful, flexible and
generally quite amazing tools. Next are *(declarative) transition systems*, which are the kind of
programs we will analyze. They are relatively simple to understand and require little encoding to
analyze them, meaning the encoding will be understandable when we look at it.

Next let's discuss *bounded model checking*, which on its own cannot (usually) prove anything: it
*just* finds counterexamples (bugs). The three posts after that discuss basic and more advanced
induction techniques.


[logics]: https://en.wikipedia.org/wiki/Mathematical_logic
[strong typing]: https://en.wikipedia.org/wiki/Strong_and_weak_typing
[borrow checker]: https://doc.rust-lang.org/1.8.0/book/references-and-borrowing.html