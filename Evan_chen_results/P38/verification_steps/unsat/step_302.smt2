(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 425984 (* 10 (pow (+ a b c) 8)) (* -196608 (pow 3 (/ 1 2)) (pow (+ (* 2 (pow a 2)) (* 2 (pow b 2)) (* 2 (pow c 2)) (* a b) (* a c) (* b c)) (pow 2 -1)))) 0)))
(check-sat)
(get-model)
(exit)