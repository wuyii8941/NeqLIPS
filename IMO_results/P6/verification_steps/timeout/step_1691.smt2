(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -2984 (pow b 4)) (* -2152 (pow a 4)) (* (pow (+ 117 (* (/ 27 2) (pow (+ (* (/ 5 3) a) (* (/ 7 3) b)) 4)) (* 800 b (pow a 3)) (* 5920 a (pow b 3))) -3) (pow (+ (* 117 a) (* 117 b) (* (/ 27 2) (pow (+ (* (/ 5 3) a) (* (/ 7 3) b)) 4)) (* 800 b (pow a 3)) (* 5920 a (pow b 3))) 4)) (* -4608 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -2304 (pow a (/ 10 3)) (pow b (/ 2 3)))) 0)))
(check-sat)
(get-model)
(exit)