(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (pow (* (+ 9 (pow (+ 1 (pow (+ (* (/ 1 2) a) (* (/ 1 2) b) (* (/ 1 2) c)) 2)) 2)) (+ (/ 1 4) (* (/ 1 4) (pow (+ a b c) 2)))) (/ 1 2)) (* -3 (pow (+ (pow a 2) (pow b 2) (* a b)) (/ 1 2))) (* -3 (pow (+ (pow a 2) (pow c 2) (* a c)) (/ 1 2))) (* -3 (pow (+ (pow b 2) (pow c 2) (* b c)) (/ 1 2)))) 0)))
(check-sat)
(get-model)
(exit)