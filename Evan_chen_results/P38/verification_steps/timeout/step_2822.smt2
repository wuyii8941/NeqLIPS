(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (pow (* (+ 9 (pow c 2)) (+ (* (/ 1 4) (pow c 2)) (* (/ 1 64) (pow b 6)))) (/ 1 2)) (* -3 (pow (+ (pow a 2) (pow b 2) (* a b)) (/ 1 2))) (* -3 (pow (+ (pow a 2) (pow c 2) (* a c)) (/ 1 2))) (* -3 (pow (+ (pow b 2) (pow c 2) (* b c)) (/ 1 2))) (* (/ 1 6) (pow (+ 121 (* 9 (pow a 4)) (* 1090 (pow a 2))) (/ 1 2))) (* a (pow (+ (* 2 (pow b 2)) (* 2 (pow c 2))) (/ 1 2))) (* b c)) 0)))
(check-sat)
(get-model)
(exit)