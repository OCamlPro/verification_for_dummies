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

; ANCHOR: cand_def
(define-fun candidate ((|s.cnt| Int)) Bool
    (>= |s.cnt| 0)
)
; ANCHOR_END: cand_def

; ANCHOR: main
(declare-const start_stop_0 Bool)
(declare-const reset_0 Bool)
(declare-const is_counting_0 Bool)
(declare-const cnt_0 Int)

(assert (init start_stop_0 reset_0 is_counting_0 cnt_0))
(assert (not (candidate cnt_0)))

; Is there a state that's initial but does not verify `candidate`?
(check-sat)
; ANCHOR_END: main
; ANCHOR_END: all