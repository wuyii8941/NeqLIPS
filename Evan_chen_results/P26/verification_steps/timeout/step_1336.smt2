(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ -3 4) (pow (* (+ 1 (pow (+ (* (/ 1 3) a) (* (/ 1 3) b) (* (/ 1 3) c)) 2)) (+ (* (pow a 2) (pow (+ (* 2 (pow a 2)) (* (pow a (/ 1 2)) (pow (+ (* (/ 1 3) a) (* (/ 1 3) b) (* (/ 1 3) c)) (/ 1 2)) (+ (* (/ 2 3) a) (* (/ 2 3) b) (* (/ 2 3) c)))) -2)) (* (pow b 2) (pow (+ (* (/ 1 3) a) (* (/ 1 3) b) (* (/ 1 3) c)) 2) (pow (+ (* (/ 1 9) (pow a 2)) (* (/ 1 9) (pow c 2)) (* (/ 19 9) (pow b 2)) (* b (+ (* (/ 1 3) a) (* (/ 1 3) b) (* (/ 1 3) c))) (* (/ 2 9) a b) (* (/ 2 9) a c) (* (/ 2 9) b c)) -2)))) (/ 1 2)) (* c (pow (+ (* (/ 1 9) (pow a 2)) (* (/ 1 9) (pow b 2)) (* (/ 19 9) (pow c 2)) (* c (+ (* (/ 1 3) a) (* (/ 1 3) b) (* (/ 1 3) c))) (* (/ 2 9) a b) (* (/ 2 9) a c) (* (/ 2 9) b c)) -1) (+ (* (/ 1 3) a) (* (/ 1 3) b) (* (/ 1 3) c)))) 0)))
(check-sat)
(get-model)
(exit)