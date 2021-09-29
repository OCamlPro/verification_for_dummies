# Verification for Dummies: SMT and Induction

By [OCamlPro][ocp].

- Adrien Champion

    <adrien.champion@ocamlpro.com>

- <a rel="license" href="http://creativecommons.org/licenses/by-sa/4.0/">
        <img
            alt="Creative Commons License"
            style="border-width:0"
            src="https://i.creativecommons.org/l/by-sa/4.0/88x31.png"
        />
    </a>

    This work is licensed under a <a
        rel="license"
        href="http://creativecommons.org/licenses/by-sa/4.0/"
    >Creative Commons Attribution-ShareAlike 4.0 International License</a>.

\
\

This book broadly discusses *induction* as a *formal verification* technique, which here really
means *formal program verification*. I will use concrete, runnable examples whenever possible.
Some of them can run directly in a browser, while others require to run small easy-to-retrieve
tools locally. Such is the case for pretty much all examples dealing directly with induction.

The next chapters discuss the following notions:

- formal logics and formal frameworks;
- SMT-solving: modern, *low-level* verification building blocks;
- declarative transition systems;
- transition system unrolling;
- BMC and induction proofs over transition systems;
- candidate strengthening.

\
\

The approach presented here is far from being the only one when it comes to program verification.
It happens to be relatively simple to understand, and I believe that familiarity with the notions
discussed here makes understanding other approaches significantly easier.

This book thus hopes to serve both as a relatively deep dive into the specific technique of
SMT-based induction, as well as an example of the technical challenges inherent to both developing
and using automated proof engines.

\
\

Some chapters contain a few pieces of Rust code. Usually to provide a runnable version of a system
under discussion, or to serve as example of actual code that we want to encode and verify. Some
notions of Rust could definitely help in places, but this is not mandatory (probably).

\
\

## Table of Contents

- [Preface](./preface)

    High-level presentation of (formal) verification as a formal method.

- [SMT Solvers](./smt)

    SMT solvers are the basic building blocks for many modern verification tools.

- [Transition Systems](./trans)

    Transition systems are *one way* to encode a wide variety of programs in a framework suited for
    formal verification. Following sections will discuss all notions in the context of transition
    systems as they are fairly easy to understand. They definitely have downsides, but one can get a
    surprising mileage out of them if careful.

- [SMT and Transition Systems](./trans_smt)

    Transition systems are represented by formulas that SMT solver can work on. This chapter lays
    out the foundation for more complex SMT-based analyses.

- [Unrolling and BMC](./bmc)

    **B**ounded **M**odel-**C**hecking is, *in general*, not a verification technique. Still, it is
    quite useful for finding *concrete counterexample*, *i.e.* a concrete behavior of the system
    that illustrates a problem. It is also a good context to showcase what one can do with a
    transition system using an SMT solver.

- [BMC: Mikino](./mikino_bmc)

    [Mikino][mikino] is a small proof engine that can perform BMC. While it requires getting
    familiar with its simple input format, it abstracts SMT solvers for us so that we can focus on
    higher-level concepts.

- [Induction](./induction)

    Induction is a natural step from BMC: it requires a simple BMC-like *base* check but also a
    *step* check which is simple to encode with SMT solvers. Since induction *is* a verification
    technique contrary to BMC, this is where we finally start proving things.

- [Induction: Mikino and Step Cex-s](./mikino_induction)

    In addition to BMC, [mikino] can also perform induction. It can thus prove *inductive*
    properties of a system. Once again, mikino abstracts the SMT solver for us. Mikino is designed
    with user experience in mind, so by the end of this chapter you will probably be able to
    experiment by modifying systems introduced so far, or write your own.

- [Candidate Strengthening](./strength)

    This chapter is quite technical and a bit theoretical. Make sure you are comfortable with all
    the notions discussed so far before diving in.

    An invariant for a system is not necessarily inductive. This last part of the series focuses on
    candidate strengthening, which is really about *discovering* useful, powerful facts about the
    system's behavior. Such facts can make non-inductive invariants inductive, which is why most
    modern induction-based verification engines focus heavily on candidate strengthening.

    This chapter, unlike previous ones, aims at proving an actual piece of code by encoding it as a
    transition system. It also touches on the complexity of verification and the notion of
    undecidability.

[mikino]: https://github.com/OCamlPro/mikino_bin (Mikino on github)
[ocp]: https://www.ocamlpro.com (OCamlPro's official website)