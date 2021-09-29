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

; State 0 is initial.
(assert
    (init start_stop_0 reset_0 is_counting_0 cnt_0)
)

; State 1 is a successor of state 0.
(assert
    (trans
        start_stop_0 reset_0 is_counting_0 cnt_0
        start_stop_1 reset_1 is_counting_1 cnt_1
    )
)

; State 2 is a successor of state 1.
(assert
    (trans
        start_stop_1 reset_1 is_counting_1 cnt_1
        start_stop_2 reset_2 is_counting_2 cnt_2
    )
)

; State 2 must falsify the candidate.
(assert
    (not (>= cnt_2 0))
)

; Is this possible?
(check-sat)
; ANCHOR_END: all