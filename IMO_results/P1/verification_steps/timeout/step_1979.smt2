(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (+ (* a b) (* a d) (* b c) (* c d)) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> d 0))
(assert (not (<= (+ (* (/ 32497973 43046721) (pow a 2)) (* (pow (+ (* (/ 1 3) (pow b 2)) (* (/ 1 3) (pow c 2)) (* (/ 5 9) d)) 2) (pow (+ (* (/ 1 3) (pow b 2)) (* (/ 1 3) (pow c 2)) (* 5 1 (pow 9 -1))) -1)) (* -1 (pow a 3) (pow (+ b c d) -1)) (* -1 (pow b 3) (pow (+ a c d) -1)) (* -1 (pow c 3) (pow (+ a b d) -1)) (* -1 (pow d 3) (pow (+ a b c) -1))) 0)))
(check-sat)
(get-model)
(exit)