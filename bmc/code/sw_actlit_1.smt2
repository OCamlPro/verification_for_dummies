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

; Transition relation.
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

; State 0.
(declare-const start_stop_0 Bool)
(declare-const reset_0 Bool)
(declare-const is_counting_0 Bool)
(declare-const cnt_0 Int)
; State 1.
(declare-const start_stop_1 Bool)
(declare-const reset_1 Bool)
(declare-const is_counting_1 Bool)
(declare-const cnt_1 Int)
; State 2.
(declare-const start_stop_2 Bool)
(declare-const reset_2 Bool)
(declare-const is_counting_2 Bool)
(declare-const cnt_2 Int)

; ANCHOR: assert_init
; State 0 is initial.
(assert
    (init start_stop_0 reset_0 is_counting_0 cnt_0)
)
; ANCHOR_END: assert_init

; ANCHOR: actlit_0_decl
; Activation literal for the first check.
(declare-const actlit_0 Bool)
; ANCHOR_END: actlit_0_decl
; ANCHOR: actlit_0_assert
; Conditional assertion of the negation of the candidate at 0.
(assert (=> actlit_0
    (not (>= cnt_0 0))
))
; ANCHOR_END: actlit_0_assert
; ANCHOR: actlit_0_check_sat
; Check-sat, assuming `actlit_0` is true.
(echo "; info: falsification at depth 0?")
(check-sat-assuming ( actlit_0 ))
; ANCHOR_END: actlit_0_check_sat
; ANCHOR: deactlit_0
; Solver answers `unsat`, we want to unroll the system some more.
; Before we do that, we deactivate the actlit.
(assert (not actlit_0))
; At this point, the solver realized the conditional assertion
; of the negation of the candidate is trivially `true`, and will
; ignore it from now on.
; ANCHOR_END: deactlit_0

; ANCHOR: sanity
(echo "; info: making sure assertion at 0 is not active anymore, expecting `sat`")
(check-sat)
; ANCHOR_END: sanity

; ANCHOR: depth_1
(assert
    (trans
        start_stop_0 reset_0 is_counting_0 cnt_0
        start_stop_1 reset_1 is_counting_1 cnt_1
    )
)
(declare-const actlit_1 Bool)
(assert (=> actlit_1
    (not (>= cnt_1 0))
))
(echo "; info: falsification at depth 1?")
(check-sat-assuming ( actlit_1 ))
(assert (not actlit_1))
(echo "; info: making sure assertion at 1 is not active anymore, expecting `sat`")
(check-sat)
; ANCHOR_END: depth_1

(assert
    (trans
        start_stop_1 reset_1 is_counting_1 cnt_1
        start_stop_2 reset_2 is_counting_2 cnt_2
    )
)
(declare-const actlit_2 Bool)
(assert (=> actlit_2
    (not (>= cnt_2 0))
))
(echo "; info: falsification at depth 2?")
(check-sat-assuming ( actlit_2 ))
(assert (not actlit_2))
(echo "; info: making sure assertion at 2 is not active anymore, expecting `sat`")
(check-sat)
; ANCHOR_END: all