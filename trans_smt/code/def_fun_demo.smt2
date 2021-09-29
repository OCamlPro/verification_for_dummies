(define-fun add_1 ( (n Int) ) Int
	(+ n 1)
)
(define-fun is_even ( (n Int) ) Bool
	(= (mod n 2) 0)
)

(declare-const n Int)
(assert
	(is_even (add_1 n))
)

; Is there an `n` such that `n + 1` is even? (yes)
(check-sat)
(get-model)