(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -2 (pow a 2)) (* -2 (pow b 2)) (* -2 (pow c 2)) (* 6 (pow (+ (* (/ 1 3) a) (* (/ 1 3) b) (* (/ 1 3) c)) 2)) (* -2 (pow (+ (pow (* (+ a b) (+ (* (/ 1 3) c) (* (/ 4 3) a) (* (/ 4 3) b))) (* 1 (pow 3 -1))) (pow (* (+ a c) (+ (* (/ 1 3) b) (* (/ 4 3) a) (* (/ 4 3) c))) (* 1 (pow 3 -1))) (pow (* (+ b c) (+ (* (/ 1 3) a) (* (/ 4 3) b) (* (/ 4 3) c))) (* 1 (pow 3 -1)))) 3) (pow (+ (* (/ 1 3) a) (* (/ 1 3) b) (* (/ 1 3) c)) 4))) 0)))
(check-sat)
(get-model)
(exit)