(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (pow (* (+ (/ 4 9) (* (/ 4 9) (pow b 2))) (+ (pow a 4) (pow b 2))) (/ 1 2)) (* (/ 2 3) (pow c 2)) (* (pow (+ a (* 5 c)) -1) (+ (* -1 (pow c 3)) (* -3 (pow a 3)))) (* (pow (+ b (* 5 a)) -1) (+ (* -1 (pow a 3)) (* -3 (pow b 3)))) (* (pow (+ c (* 5 b)) -1) (+ (* -1 (pow b 3)) (* -3 (pow c 3))))) 0)))
(check-sat)
(get-model)
(exit)