; ANCHOR: all
; ANCHOR: trans_def
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
; ANCHOR_END: trans_def

; ANCHOR: states_def
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
; State 3.
(declare-const start_stop_3 Bool)
(declare-const reset_3 Bool)
(declare-const is_counting_3 Bool)
(declare-const cnt_3 Int)
; ANCHOR_END: states_def

; ANCHOR: unroll_1
(assert (trans
    start_stop_0 reset_0 is_counting_0 cnt_0
    start_stop_1 reset_1 is_counting_1 cnt_1
))
(assert (trans
    start_stop_1 reset_1 is_counting_1 cnt_1
    start_stop_2 reset_2 is_counting_2 cnt_2
))
(assert (trans
    start_stop_2 reset_2 is_counting_2 cnt_2
    start_stop_3 reset_3 is_counting_3 cnt_3
))
; ANCHOR_END: unroll_1

; ANCHOR: state_constraints
(assert (and
    ; starting from `cnt > 7`,
    (> cnt_0 7)
    ; can we reach a state where `cnt = 5` in three transitions?
    (= cnt_3 5)
))

(check-sat)
; ANCHOR_END: state_constraints
; ANCHOR_END: all