; ANCHOR: all
; ANCHOR: init_def
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
;       ^^^^^^^^^^^^^^~~~~ fixed the specification
    )
)
; ANCHOR_END: init_def

; ANCHOR: states_def
(declare-const start_stop_0 Bool)
(declare-const reset_0 Bool)
(declare-const is_counting_0 Bool)
(declare-const cnt_0 Int)
; ANCHOR_END: states_def

; ANCHOR: assert_init
(assert
    (init start_stop_0 reset_0 is_counting_0 cnt_0)
)
; ANCHOR_END: assert_init

; ANCHOR: state_constraints
(assert
    (not (>= cnt_0 0))
)

(check-sat)
; ANCHOR_END: state_constraints
; ANCHOR_END: all