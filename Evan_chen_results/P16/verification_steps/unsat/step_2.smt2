(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -18 (pow (+ (* 2 a) (* 2 b) (* 2 c)) -1)) (* 9 (pow (+ a b c) -1))) 0)))
(check-sat)
(get-model)
(exit)