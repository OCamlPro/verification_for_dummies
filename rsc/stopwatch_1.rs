/// Variables.
vars: (
    /// Stop and reset (inputs).
    start_stop, reset: bool
    /// Internal variables.
    is_running: bool
    /// Time counter (output).
    cnt: int
)

/// Initial predicate.
init: (and
    (= cnt 0)
    (not is_running)
)

/// Transition relation.
trans: (and
    (= is_running (ite start_stop (not is_running) is_running))
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
    "cnt is positive": (≥ cnt 0)
    "cnt is not -7": (not (= cnt (- 7)))
    "if reset then cnt is 0": (⇒ reset (= cnt 0))
)
