(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -95488 (pow b 4)) (* -68864 (pow a 4)) (* 234 (pow (+ (* 2 a) (* 2 b)) 4)) (* -221184 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 25600 b (pow a 3)) (* 110592 (pow a (/ 5 3)) (pow b (/ 7 3))) (* 189440 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)