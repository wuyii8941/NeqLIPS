(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -1375 (pow b 4)) (* -823 (pow a 4)) (* (pow (+ 318 (* 172 b (pow a 3)) (* 1296 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 1296 (pow a (/ 5 3)) (pow b (/ 7 3)))) -1) (pow (+ (* 172 b (pow a 3)) (* 318 a b) (* 1296 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 1296 (pow a (/ 5 3)) (pow b (/ 7 3)))) 2)) (* -1728 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -864 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 1708 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)