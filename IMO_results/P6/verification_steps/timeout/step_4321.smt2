(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -678660864 (pow b 4)) (* -520588032 (pow a 4)) (* (pow (+ (* 79916544 (pow b 2)) (* 741331968 b (pow a 3)) (* 2416432128 a (pow b 3))) -1) (pow (+ (* 79916544 a (pow b 2)) (* 741331968 b (pow a 3)) (* 2416432128 a (pow b 3))) 2)) (* -1358954496 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -679477248 (pow a (/ 10 3)) (pow b (/ 2 3)))) 0)))
(check-sat)
(get-model)
(exit)