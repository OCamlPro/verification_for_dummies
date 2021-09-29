; ANCHOR: all
; Initial predicate.
(define-fun init
    (
        (|s.start_stop| Bool)
        (|s.reset| Bool)
        (|s.is_counting| Bool)
        (|s.cnt| Int)
    )
    Bool

    (and
        (= |s.is_counting| |s.start_stop|)
        (=> |s.reset| (= |s.cnt| 0))
        (>= |s.cnt| 0)
    )
)
(define-fun trans
    (
        ; "Previous" state.
        (|s.start_stop| Bool)
        (|s.reset| Bool)
        (|s.is_counting| Bool)
        (|s.cnt| Int)
        ; "Next" state.
        (|s'.start_stop| Bool)
        (|s'.reset| Bool)
        (|s'.is_counting| Bool)
        (|s'.cnt| Int)
    )
    Bool

    (and
        (=> |s'.start_stop|
            (= |s'.is_counting| (not |s.is_counting|))
        )
        (=> (not |s'.start_stop|)
            (= |s'.is_counting| |s.is_counting|)
        )
        (= |s'.cnt|
            (ite |s'.reset|
                0
                (ite |s'.is_counting|
                    (+ |s.cnt| 1)
                    |s.cnt|
                )
            )
        )
    )
)

(define-fun candidate ((|s.cnt| Int)) Bool
    (>= |s.cnt| 0)
)


(declare-const start_stop_0 Bool)
(declare-const reset_0 Bool)
(declare-const is_counting_0 Bool)
(declare-const cnt_0 Int)

; Wait, shouldn't this be under an activation literal?
(assert (not (candidate cnt_0)))
; No because we're being very clever. More on that in the
; step check below.

(echo "base check, expecting `unsat`")
(declare-const base_actlit Bool)
(assert (=> base_actlit
    (init start_stop_0 reset_0 is_counting_0 cnt_0)
))
(check-sat-assuming (base_actlit))


(declare-const start_stop_1 Bool)
(declare-const reset_1 Bool)
(declare-const is_counting_1 Bool)
(declare-const cnt_1 Int)

(echo "step check, expecting `unsat`")
(assert
    (trans
        ; State `1` is first?
        start_stop_1 reset_1 is_counting_1 cnt_1
        ; State `0` is its successor?
        start_stop_0 reset_0 is_counting_0 cnt_0
    )
)
(assert (candidate cnt_1))
; Most unhorthodox. We are reverse-unrolling™.
; When we checked for base above, we asserted `(not (candidate cnt_0))`
; **unconditionnaly**. So at this point, we have
; - candidate(s_1)
; - trans(s_1, s_0)
; - ¬candidate(s_0)
;
; By unrolling backwards, with `s_0` the *last* state, we can reverse-unroll
; without changing anything, just adding a state `s_2` and asserting
; `trans(s_2, s_1)`.
;
; This is useful when doing "k-induction", which requires unrolling more than
; once in step (and base), and because SMT-solvers work by **learning** facts
; about the SMT instance they work on. These facts are *kept between checks*.
; So, Z3 will learn facts from the three assertions above in the `check-sat`
; below. If we reverse-unroll once more by adding an `s_2` as the predecessor
; of `s_1`, then Z3 will be able to re-use facts it learnt since we only added
; to the instance, but did not change anything that was there.

(check-sat)

(echo "induction proof complete")
; ANCHOR_END: all