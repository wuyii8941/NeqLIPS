(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 24 (* -12 (pow (+ (* 96 (pow a 2)) (* 96 (pow b 2)) (* 96 (pow c 2)) (* 48 a b) (* 48 a c) (* 48 b c)) (pow 2 -1))) (* 2 (+ 4 (pow (+ a b c) 2)) (+ a b c))) 0)))
(check-sat)
(get-model)
(exit)