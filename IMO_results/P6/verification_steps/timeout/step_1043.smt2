(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -95488 (pow b 4)) (* -68864 (pow a 4)) (* (pow (+ (* 3744 (pow a 4)) (* 3744 (pow b 2)) (* 22464 (pow a 2) (pow b 2))) -1) (pow (+ (* 3744 (pow a 4)) (* 3744 (pow b 3)) (* 22464 (pow a 2) (pow b 2))) 2)) (* -147456 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -73728 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 40576 b (pow a 3)) (* 110592 (pow a (/ 5 3)) (pow b (/ 7 3))) (* 204416 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)