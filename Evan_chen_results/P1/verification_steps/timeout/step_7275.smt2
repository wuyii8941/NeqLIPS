(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (+ (* a b) (* a d) (* b c) (* c d)) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> d 0))
(assert (not (<= (+ (* (/ 1 39366) (pow (+ (* 172186884 (pow c 4)) (* 172186884 (pow d 4)) (* 387420489 (pow c 2)) (* 387420489 (pow d 2)) (* 790172100 (pow a 4)) (* 344373768 (pow c 2) (pow d 2)) (* 351187600 (pow a 4) (pow c 2)) (* 351187600 (pow a 4) (pow d 2))) (/ 1 2))) (* (/ 5 9) (pow b 2)) (* -1 (pow a 3) (pow (+ b c d) -1)) (* -1 (pow b 3) (pow (+ a c d) -1)) (* -1 (pow c 3) (pow (+ a b d) -1)) (* -1 (pow d 3) (pow (+ a b c) -1))) 0)))
(check-sat)
(get-model)
(exit)