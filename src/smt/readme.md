# SMT Solvers

> SMT solvers are basic building blocks for most modern verification tools. While studying SMT
> solvers is particularly rewarding for developing such tools, understanding SMT forces to grasp
> concepts that are very useful even for high-level users. Later chapters will rely heavily on SMT
> solvers and readers are encouraged to run and modify examples themselves, or even create new ones.

\
\

Let's go over a few theory-level notions before we actually start playing with SMT solvers. A
**S**atisfiability **M**odulo **T**heory (SMT) solver is a solver for establishing whether some
constraints expressed in **M**any-**S**orted **F**irst **O**rder **L**ogic (MSFOL) are
*satisfiable*. Let's unpack this.

First, MSFOL is built on FOL (**F**irst **O**rder **L**ogic), which basically means *"boolean
formulas"*. For instance, `a ∧ (false ∨ b ∨ c)` is a FOL formula, where `∧` is conjunction (`&&`)
and `∨` is disjunction (`||`). So this formula *evaluates* to `true` if and only if `a` is `true`
and either `b` or `c` is `true` (since `false` tends not to be `true`). We can represent this
formula as a tree, where leaves are boolean literals and nodes are boolean operators.

```text
 ┌───∧───┐
 │       │
 a    ┌──∨──┬───────┐
      │     │       │
      │     │       │
    false   b       c
```

The leaves of the tree are *atoms*. MSFOL essentially extends FOL by allowing atoms to be formulas
in other theories such as integers, strings, arrays, *etc.* For instance, with `x` and `y` integers
and `arr` an array:

```text
   ┌───∧─────┐
   │         │
 x > 7    ┌──∨────┬───────┐
          │       │       │
          │       │       │
        false   y ≤ x   arr[y] = x + 1
```

Note that the last atom, `arr[y] = x + 1`, mixes array selection `arr[y]` with addition over
integers `x + 1`.


## Z3

Examples in the next sections (and the next chapter) will rely on the [Z3 SMT solver][z3] to
actually run. You can build it from source or recover a binary from the [release page][z3 release].
The version should not matter too much for what we'll do, but for reference this guide used
`v4.8.12`.

From this point forward I assume readers have a Z3 binary called `z3` in their path. That is,
running the command `z3 -version` should not fail and produce an output similar to

```text
Z3 version 4.8.13 - 64 bit
```

While I recommend Z3, other efficient solvers exist and include [Alt-Ergo][ae], [CVC4][cvc4] and
[Yices 2][yices]. Solvers tend to be good at distinct kinds of problem from each other, and
verification frameworks routinely run several of them in parallel, wait for the quickest answer,
and discard solver instances that are still running.

<!-- Last, while we recommend having Z3 available locally, you can run the examples in this section
using only the [Z3 online playground][z3 online]. Beware that all following chapters about induction
require to have Z3 in your path. -->

\
\



## Satisfiability

Formula satisfiability is concerned about whether it is possible to make some formula evaluate to
`true`. More precisely, is it possible to find a valuation for the variables appearing in the
formula under which the formula is `true`. Such a valuation is called a *model* of the formula. Let
us write a tiny example and start running Z3 to play with satisfiability directly.

> To be precise, *SAT* stands for the *boolean satisfiability problem*, which deals with finding
> models for purely boolean formulas. *"SMT"* adds *"Modulo Theory"* to *"Satisfiability"* to
> specify that atoms of the formula can mention theories different from booleans (integers, reals,
> arrays, *etc.*) in its atoms, and that models must respect the rules of these theories.

\
\



## SMT-LIB 2

For simplicity's sake, let's only allow atoms to mention integers. Consider the following formula.

```text
(declare-const x Int)
(declare-const y Int)

   ┌───∧─────┐
   │         │
 x > 7    ┌──∨──────┐
          │         │
          │         │
        y = 2*x   x = 11
```

The first two lines declare *"constants"* `x` and `y`. As programmers, we can see them as
*"variables"* in the sense that they represent an unknown value of type `Int`. This syntax comes
from the [SMT-LIB 2 standard][smt lib], which is the standard *scripting* language for interacting
with SMT solvers. Most, if not all, SMT solvers support SMT-LIB 2 input.

Of course, the ASCII art tree representing the formula is *not* legal SMT-LIB 2. An SMT-LIB 2 script
declares constants (and more) and uses these constants to *assert* formulas, *i.e.* specify to the
solver what the constraints are.

Also, SMT-LIB formulas are written using *prefix notation* (or *Polish notation*). For instance, `y
= 2*x` would be written `(= y (* 2 x))`. This is a compromise between ease of printing/parsing and
human readability. SMT-LIB is really meant to be used by programs to communicate, not for humans to
actually write by hand. Still, it is readable enough for pedagogic and debugging purposes.

> [VS Code] has an extension for SMT-LIB syntax highlighting (`.smt2` files). The pieces of SMT-LIB
> code I will show in this book will not have syntax highlighting, unfortunately. I apologize
> for this problem, and encourage readers to copy these pieces of code in an editor that supports
> SMT-LIB using the button at the top-right of the code blocks.

Anyway, an SMT-LIB assertion of our running example would look like this:

```text
{{ #include code/ex_1.smt2 }}
```

The `assert` command feeds a constraint to the solver. Next, we can ask the solver to check
the satisfiability of all the constraints (of which there is just one here) with `check-sat`.


## Playing with Z3: `sat`

Let's now run Z3 on this tiny example. Create a file `test.smt2` and copy the content of the
SMT-LIB script above. No special option is needed and you should get the following output.

```text
❯ z3 test.smt2
{{ #include code/ex_1.smt2.out }}
```

Z3 simply answered `sat`, indicating that the formula is *"satisfiable"*: there exists a model (a
valuation of the variables) that make our constraints `true`. This is nice, but it would be better
if Z3 could give us a model to make sure it is not lying to us (it's not). We can do so by adding a
`get-model` command after the `check-sat`. (Note that `get-model` is **only** legal after a
`check-sat` yielded `sat`.)

```text
{{ #include code/ex_2.smt2 }}
```

After updating `test.smt2`, running Z3 again will produce a model. You might not get exactly the
same model as the one reported here depending on the precise version of Z3 you are using and
possibly other factors (such as your operating system).

```text
❯ z3 test.smt2
{{ #include code/ex_2.smt2.out }}
```

The model is slightly cryptic. Z3 defines `x` and `y` as functions taking no arguments, which means
that they are constants. This is because all functions are *pure* in SMT-LIB, meaning they always
produce the same output when given the same inputs. Hence, a function with no arguments can only
produce one value, and is therefore the same as a constant. In fact, `(define-fun <ident> () <type>
<val>)` is the same as `(define-const <ident> <type> <val>)`, and the `(declare-const <ident>
<type>)` we used in the SMT-LIB script is equivalent to `(declare-fun <ident> () <type>)`. Again,
in SMT-LIB (and pure functional languages) a constant is just a function that takes no argument.

This valuation is a model because `(> x 7) ≡ (> 8 7)` holds and so does `(= y (* 2 x)) ≡ (= 16 (* 2
8))`.

\
\

Now, remember that we can assert more than one constraint, and that Z3 works on the conjunction of
all constraints. In our running example, our only constraint is a conjunction, meaning we could
write it as two constraints.

```text
{{ #include code/ex_3.smt2 }}
```

Let's now add the constraint that `y` is an odd number: `(= (mod y 2) 1)`. This should void the
previous model, and more generally any model that relies on making `(= y (* 2 x))` true to satisfy
the constraints. (Since `y` would need to be both even and odd.)

```text
{{ #include code/ex_4.smt2 }}
```

We now get

```text
❯ z3 test.smt2
{{ #include code/ex_4.smt2.out }}
```

As expected, Z3 now has to make the second constraint `true` through `(= x 11)`.


## Playing with Z3: `unsat`

Let's add another constraint to make these constraints unsatisfiable. In the latest version of our
example, Z3 has no choice but to have `x` be `11` since it is the only way to verify the second
constraint (because the third constraint prevents `y` from being even).

We can simply constrain `x` to be even (which prevents `x` to be `11`), which we will write as "`x`
cannot be odd".

```text
{{ #include code/ex_5.smt2 }}
```

Z3 knows exactly what we are doing and replies that the formula is unsatisfiable.

```text
❯ z3 test.smt2
{{ #include code/ex_5.smt2.out }}
```

We get an error though, because it does not make sense to ask for a model if the formula is
unsatisfiable. *"Unsatisfiable"*, or *unsat*, means *"has no model"* (*i.e.* no valuation of the
variables can make all constraints true).

\
\

Now, what does this unsatisfiability result tell us? One way to see it is to consider the first
three constraints as some form of context. That is, the first three constraints correspond to some
point in a program where there are two unknown values `x` and `y`, and the first three constraints
encode what we know to be true about these values.

The last constraint can be seen as a question. Say that at that point in the program, there is an
assertion that `x` must be odd. We want to verify that this assert can never fail. From this point
of view, then the latest version of our running example amounts to asking "given the context (first
three constraints), is it possible for `x` to **not** be odd?". In other words, we are asking Z3 to
find some values that both verify our context and **falsify** the program's assertion.

Z3 answers "no": in this context, it is not possible for `x` not to be odd. This means that Z3
proved for us that the program's assert statement can never fail (and can be compiled away).

What if, with different constraints, the negation of the program's assert statement was
satisfiable? Then, [as we saw in the previous section](#playing-with-z3-sat), Z3 can give us a
*model*: a valuation of all the (relevant) variables involved in the check. this constitutes a
*counterexample*, which shows how it is possible to verify the whole context but still falsify the
program assertion (*i.e* satisfy the SMT-LIB-level `(assert (not <program_assertion>))`).

## Outro

SMT solvers are extremely powerful, flexible and expressive tools. *Powerful* because they are
highly optimized tools constantly improved by ongoing theoretical and practical research.
*Flexible* because many different theories are available, allowing to manipulate integers, strings,
arrays, algebraic data types, *etc.* And *expressive* because a great deal of verification problems
are amenable to SMT without too much trouble.

One such verification problem is *declarative transition system (induction-based) verification*, as
we will see in the following chapters.

\
\

The next section is optional, it is a repetition of the present section using [mikino][mikino
repo]'s version of SMT-LIB 2: *hsmt*. Hsmt is a Rust-flavored syntax for (a subset of) the SMT-LIB
2 scripting language. As we will see, mikino's primary functionality is performing SMT-based
induction checks; hsmt is just a by-product feature that I thought could be useful for teaching
what SMT is and how to interact with SMT solvers. Note that while mikino only supports a subset of
SMT-LIB 2 (function definitions are not supported for example), it also adds new features such as
conditional branching (if-then-else) over check-sat results.

If that's not interesting for you right now, feel free to move on directly to [the next
chapter](../trans).



[z3]: https://github.com/Z3Prover/z3 (Z3 on github)
[z3 release]: https://github.com/Z3Prover/z3/releases (Z3's releases on github)
<!-- [z3 online]: https://rise4fun.com/z3 (Z3's online interface) -->
[ae]: https://alt-ergo.ocamlpro.com (Alt-Ergo homepage)
[cvc4]: https://cvc4.github.io/ (CVC4 homepage)
[yices]: https://yices.csl.sri.com (Yices 2 homepage)
[smt lib]: http://smtlib.cs.uiowa.edu (SMT-LIB homepage)
[VS Code]: https://code.visualstudio.com (VS Code homepage)
[mikino repo]: https://github.com/OCamlPro/mikino_bin (Mikino binary repository)
