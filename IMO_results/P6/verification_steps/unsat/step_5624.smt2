(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -14478098432 (pow b 4)) (* -11105878016 (pow a 4)) (* (pow (+ 106555392 (* 745887744 (pow b 2))) -1) (pow (+ (* 106555392 (pow a 2)) (* 106555392 (pow b 3)) (* 639332352 a (pow b 2))) 2)) (* -28991029248 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -14495514624 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 16241303552 b (pow a 3)) (* 51976773632 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)