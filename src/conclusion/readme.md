# Conclusion

If you have understood (most of) what we have discussed, congratulations 🎉. I hope some readers
might be encouraged to develop cool verification tools, while others got enough of an understanding
on the topic of verification to have a more expert usage of verification tools, *if* (and most
likely *when*) they start using such tools as developers.

## Related Things

Transition systems are not the only way to encode program verification problems. [Constrained Horn
Clauses][horn] (CHC-s) are very popular at the time of writing, and for good reasons. Basically,
CHC-s represent a program (or program-like structure) in a more fragmented way than transition
systems. Techniques based on a CHC representation tend to have a fine-grain vision of the notion of
*transition*, which allows for more precision (efficiency) in the verification approach built on
top of it.

Besides pure induction, there are many other techniques that are worth looking into. A pretty
important one is **P**roperty **D**irected **R**eachability (PDR), also known as **I**ncremental
**C**onstruction of **I**nductive **C**lauses for **I**ndubitable **C**orrectness (IC3).
Unfortunately, PDR/IC3 is mostly discussed in academic papers and I could not find a presentation
understandable without a serious background in formal logics. This is partially due to the fact
that PDR is still quite recent, but also to its complex and intricate nature. Here are a few links
though, all of them are **PDF**:

- [original paper][ic3]
- [efficient PDR][pdr]
- [IC3 + k-induction][gurfinkel]

It should be noted that PDR is particularly interesting in the purely propositional case. That is,
for systems that can be expressed using nothing but booleans. Systems using arithmetic, arrays,
strings... are more difficult to handle because of one of the necessary PDR steps (pre-image
computation), as well as certain crucial optimization that only apply on purely propositional
formulas.


[horn]: https://en.wikipedia.org/wiki/Horn_clause
(Horn Clauses on wikipedia)
[ic3]: http://alcom.ee.ntu.edu.tw/system/privatezone/meetingfile/201010222258251.pdf
[pdr]: https://www.cs.utexas.edu/~ragerdl/fmcad11/papers/7.pdf
[gurfinkel]: https://www.cs.utexas.edu/users/hunt/FMCAD/FMCAD17/preprints/s6p3.pdf