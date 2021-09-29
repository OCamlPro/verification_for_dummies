/// Variables.
vars: (
    /// Stop and reset (inputs).
    start_stop, reset: bool
    /// Internal variables.
    is_running, start_stop_confirmed: bool
    start_stop_count: int
    /// Time counter (output).
    cnt: int
)

/// Initial predicate.
init: (and
    (= cnt 0)
    (= start_stop_count 0)
    (not start_stop_confirmed)
    (not is_running)
)

/// Transition relation.
trans: (and
    (= start_stop_count
        (ite
            (= (pre start_stop_count) 3)
            0
            (ite
                start_stop
                (+ (pre start_stop_count) 1)
                0
            )
        )
    )
    (= start_stop_confirmed (= start_stop_count 3))
    (= is_running (ite start_stop_confirmed (not is_running) is_running))
    (= cnt
        (ite
            // condition
            reset
            // then
            0
            // else
            (ite
                // condition
                is_running
                // then
                (+ (pre cnt) 1)
                // else
                (pre cnt)
            )
        )
    )
)

/// Proof obligations.
po_s: (
    "blah": (not start_stop_confirmed)
    "blih": (≤ cnt 111)
    "confirmation bounds": (and (≤ 0 start_stop_count) (≤ start_stop_count 2))
    "cnt is positive": (≥ cnt 0)
    "cnt is not -7": (not (= cnt (- 7)))
    "if reset then cnt is 0": (⇒ reset (= cnt 0))
)
