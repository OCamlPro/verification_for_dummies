(declare-const x Int)
(declare-const y Int)

(assert (and
	(> x 7)
	(or (= y (* 2 x)) (= x 11))
))

(check-sat)
(get-model)