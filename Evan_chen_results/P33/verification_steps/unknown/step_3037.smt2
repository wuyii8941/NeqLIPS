(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 5 (* 2 a) (* 2 c) (* 2 (pow b 2)) (* -4 (pow 3 (/ 1 2)) (pow (+ a b c (* a b) (* a c) (* b c)) (pow 2 -1))) (* 2 a (pow 2 (/ 1 2))) (* 2 c (pow 2 (/ 1 2)))) 0)))
(check-sat)
(get-model)
(exit)