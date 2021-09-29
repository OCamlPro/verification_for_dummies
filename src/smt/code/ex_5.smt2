(declare-const x Int)
(declare-const y Int)

(assert (> x 7))
(assert (or (= y (* 2 x)) (= x 11)))
(assert (= (mod y 2) 1))

(assert (not (= (mod x 2) 1)))

(check-sat)
(get-model)