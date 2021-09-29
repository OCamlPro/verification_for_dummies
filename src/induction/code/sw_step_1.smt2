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

; ANCHOR: cand_def
(define-fun candidate ((|s.cnt| Int)) Bool
    (>= |s.cnt| 0)
)
; ANCHOR_END: cand_def

; ANCHOR: var_decls
; Previous state.
(declare-const start_stop_0 Bool)
(declare-const reset_0 Bool)
(declare-const is_counting_0 Bool)
(declare-const cnt_0 Int)
; Next state.
(declare-const start_stop_1 Bool)
(declare-const reset_1 Bool)
(declare-const is_counting_1 Bool)
(declare-const cnt_1 Int)
; ANCHOR_END: var_decls

; ANCHOR: main
(assert (candidate cnt_0))
(assert (trans
    start_stop_0 reset_0 is_counting_0 cnt_0
    start_stop_1 reset_1 is_counting_1 cnt_1
))
(assert (not (candidate cnt_1)))

; Is there a state verifying `candidate` that can
; reach a state falsifying it in one transition?
(check-sat)
; ANCHOR_END: main
; ANCHOR_END: all