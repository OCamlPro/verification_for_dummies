# SMT Scripts: Mikino

This section as well as most following ones rely on [mikino][mikino repo], a nice tool I wrote for
interacting with SMT solvers and perform induction-based analyses (which we will do soon). If you
want to follow along just make sure [you have mikino set up](../mikino_install). Be careful that
mikino requires Z3 to actually run, as discussed in the [setup instructions](../mikino_install).

\

Mikino has its own scripting language for interacting with SMT solvers. It is basically a
Rust-flavored version of [SMT-LIB 2][smt lib] called *hsmt* (Human SMT). While readable, SMT-LIB 2
is designed to be written and parsed by programs, not humans. You probably noticed this yourself
reading the previous section.

We want to emphasize that mikino is **not** an SMT solver: when running hsmt scripts, mikino acts
as a thin layer between the hsmt code and Z3. Mikino translates your commands, passes them to Z3,
and handles/prettifies the result of the command if any. Whenever we say *mikino does something* in
this section, it's really Z3 doing through mikino.

\

We're going to go through what hsmt is shortly, but before we do know that you can run `mikino demo
--script demo.rs` to generate a demo script file `demo.rs` which discusses more details about hsmt
that we can cover here. For instance, the demo discusses conditional branching (if-then-else) over
check-sat results (which SMT-LIB 2 does not have) which will not be mentioned here.



## Basics

Consider the following formula.

```text
vars {
   x y : int
}

   ┌───∧─────┐
   │         │
 x > 7    ┌──∨──────┐
          │         │
          │         │
        y = 2*x   x = 11
```

Of course, the ASCII art tree representing the formula is *not* legal hsmt. An hsmt script declares
variables and uses them to *assert* formulas, *i.e.* specify to the solver what the constraints on
these variables are.



As you already guessed the first lines in the snippet above declare integer variables `x` and `y`.
`vars` block let you declare variables of type `int`, `bool` or `rat`(ional) as a comma-separated
(with optional trailing comma) list:

```rust ,compile_fail
vars {
   x y : int,
   flag1 : bool,
   flag2 : bool,
   z1 z2 z3 : rat,
}
```

Anyway, an hsmt assertion of our running example would look like this:

```rust ,compile_fail
{{ #include code/ex_1.hsmt:all }}
```

All hsmt commands (`vars`, `assert`, `check_sat`, ...) accept their input either in a block `{ ...
}` or between parens `( ... )`.

The `assert` command feeds a constraint to the solver as a constraint. Next, we can ask the solver
to check the satisfiability of all the constraints (of which there is just one here) with
`check-sat`.


## Playing with mikino: `sat`

Let's now run mikino on this tiny example. Create a file `test.rs` and copy the content of the
SMT-LIB script above. No special option is needed and you should get the following output.

```text
> mikino script test.rs
{{ #include code/ex_1.hsmt.out }}
```

Mikino answered `sat`, indicating that the formula is *"satisfiable"*: there exists a model (a
valuation of the variables) that make our constraints (just one in this case) `true`. This is nice,
but it would be better if mikino could give us a model to make sure it is not lying to us (it's
not). We can do so by adding a `get_model!()` command after the `check_sat!()`. (Note that
`get_model!()` is **only** legal after a `check_sat!()` yielded `sat`.)

```rs
{{ #include code/ex_2.hsmt:all }}
```

After updating `test.rs`, running mikino again will produce a model. You might not get exactly the
same model as the one reported here depending on the precise version of mikino/Z3 you are using and
possibly other factors (such as your operating system).

```text
> mikino script test.rs
{{ #include code/ex_2.hsmt.out }}
```



This valuation is a model because `(> x 7) ≡ (> 8 7)` holds ("is true") and so does `(= y (* 2 x))
≡ (= 16 (* 2 8))`: all constraints are verified.

> By the way, you might see a pattern here with the use of `!` after some commands' name. It is not
> mandatory, but all commands that either *i)* can produce an output like `check_sat`, `get_model`,
> `echo`, `println`, or *ii)* exit/crash the script (`exit`, `panic`) can be written with a `!` at
> the end like `assert!()`, `println!("my message")`... to make them stand out visually.

\
\

Now, we can assert more than one constraint. Mikino works on the conjunction of all constraints
---or at least Z3, behind the scene, does. In our running example, our only constraint is a
conjunction, meaning we could write it as two constraints.

```rust ,compile_fail
{{ #include code/ex_3.hsmt:all }}
```

```text
> mikino script test.rs
{{ #include code/ex_3.hsmt.out }}
```

Alternatively, `assert` actually takes as input a comma-separated list (with optional trailing
comma) of expressions, understood as a conjunction. So this also works:

```rust ,compile_fail
{{ #include code/ex_3_variant.hsmt:all }}
```

```text
> mikino script test.rs
{{ #include code/ex_3_variant.hsmt.out }}
```

\
\



Let's now add the constraint that `y` is an odd number: `y % 2 = 1`. This should void the previous
model, and more generally any model that relies on making `y = 2*x` true to satisfy the constraints
since `y` would need to be both even and odd.

```rust ,compile_fail
{{ #include code/ex_4.hsmt:all }}
```

We now get

```text
> mikino script test.rs
{{ #include code/ex_4.hsmt.out }}
```

As expected, the solver now has to make the second constraint `true` through `x = 11`.




## Playing with mikino: `unsat`

Let's add another constraint to make our problem `unsat`isfiable. In the latest version of our
example, the solver has no choice but to have `x` be `11` since it is the only way to verify the
second constraint (because the third constraint prevents `y` from being even).

We can simply constrain `x` to be even (which prevents `x` from being `11`), which we will write as
"`x` cannot be odd".

```rust ,compile_fail
{{ #include code/ex_5.hsmt:all }}
```

Z3 knows exactly what we are doing and replies that the formula is unsatisfiable.

```text
❯ z3 test.rs
{{ #include code/ex_5.hsmt.out }}
```

We get an error though, because it does not make sense to ask for a model if the formula is
unsatisfiable. *"Unsatisfiable"*, or *unsat*, means *"has no model"*, *i.e.* no valuation of the
variables can make all constraints true.

\
\

Now, what does this unsatisfiability result tell us? One way to see it is to consider the first
three constraints as some form of context. That is, the first three constraints correspond to some
point in a program where there are two unknown values `x` and `y`, and the first three constraints
encode what we know to be true about these values.

The last constraint can be seen as a question. Say that at that point in the program, there is an
assertion that `x` must be odd. We want to verify that it can never fail. From this point of view,
then the latest version of our running example amounts to asking "given the context (first three
constraints), is it possible for `x` to **not** be odd?". In other words, we are asking the solver
to find some values that both verify our context and **falsify** the program's assertion.

The solver answers *"no"*: in this context, it is not possible for `x` not to be odd. This means
that we proved for us that the program's assertion can never fail (and can be compiled away). More
precisely, we proved that **our encoding of the program's assertion** can never fail. Whatever we
then do with this information depends on how much trust we have in the encoding.

\
\

What if, with different constraints, the negation of the program's assert statement was
satisfiable? Then, [as we saw in the previous section](#playing-with-z3-sat), solvers can give us a
*model*: a valuation of all the (relevant) variables involved in the check. this constitutes a
*counterexample*, which shows how it is possible to verify the whole context but still falsify the
program assertion, *i.e* satisfy `assert { ¬ <program_assertion> }`.

## Outro

SMT solvers are extremely powerful, flexible and expressive tools. *Powerful* because they are
highly optimized tools constantly improved by ongoing theoretical and practical research.
*Flexible* because many different theories are available, allowing to manipulate integers, strings,
arrays, algebraic data types, *etc.* And *expressive* because a great deal of verification problems
are amenable to SMT without too much trouble.

One such verification problem is *declarative transition system (induction-based) verification*, as
we will see in the following chapters.




[z3]: https://github.com/Z3Prover/z3 (Z3 on github)
[z3 release]: https://github.com/Z3Prover/z3/releases (Z3's releases on github)
<!-- [z3 online]: https://rise4fun.com/z3 (Z3's online interface) -->
[ae]: https://alt-ergo.ocamlpro.com (Alt-Ergo homepage)
[cvc4]: https://cvc4.github.io/ (CVC4 homepage)
[yices]: https://yices.csl.sri.com (Yices 2 homepage)
[VS Code]: https://code.visualstudio.com (VS Code homepage)

[smt lib]: http://smtlib.cs.uiowa.edu (SMT-LIB homepage)
[mikino repo]: https://github.com/OCamlPro/mikino_bin (Mikino binary repository)