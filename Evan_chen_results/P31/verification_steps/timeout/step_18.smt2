(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (/ 3 2) (pow a 2)) (* (/ 3 2) (pow b 2)) (* (/ 3 2) (pow c 2)) (* -1 (pow (+ (pow (* (+ a (* 3 c)) (+ (pow c 3) (* 5 (pow a 3)))) (* 1 (pow 3 -1))) (pow (* (+ b (* 3 a)) (+ (pow a 3) (* 5 (pow b 3)))) (* 1 (pow 3 -1))) (pow (* (+ c (* 3 b)) (+ (pow b 3) (* 5 (pow c 3)))) (* 1 (pow 3 -1)))) 3) (pow (+ (* 4 a) (* 4 b) (* 4 c)) -2))) 0)))
(check-sat)
(get-model)
(exit)