(declare-const x Int)
(declare-const y Int)

(assert (> x 7))
(assert (or (= y (* 2 x)) (= x 11)))

(check-sat)
(get-model)