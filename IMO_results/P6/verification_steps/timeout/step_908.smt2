(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -5734 (pow b 4)) (* -4070 (pow a 4)) (* (pow (+ 1404 (* 2536 b (pow a 3)) (* 6912 (pow a (/ 5 3)) (pow b (/ 7 3)))) -1) (pow (+ (* 1404 a b) (* 2536 b (pow a 3)) (* 6912 (pow a (/ 5 3)) (pow b (/ 7 3)))) 2)) (* -9216 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -4608 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 12776 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)