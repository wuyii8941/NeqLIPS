(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -128 (pow b 4)) (* -64 (pow a 4)) (* (pow (+ 48 (* 3 (pow (+ a b) 4))) -3) (pow (+ (* 3 (pow (+ a b) 4)) (* 8 a) (* 40 b)) 4)) (* -128 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -64 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 96 a (pow b 3)) (* 96 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 96 (pow a (/ 5 3)) (pow b (/ 7 3)))) 0)))
(check-sat)
(get-model)
(exit)