(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ (* a b) (* a c) (* b c)) 1))
(assert (<= (* a b c) (* (/ 1 9) (pow 3 (/ 1 2)))))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 1 2) (pow (+ (pow b -1) (* 6 c)) (pow 3 -1)) (pow (+ (pow c -1) (* 6 a)) (pow 3 -1)) (* (/ 1 2) (pow (+ (pow a -1) (* 6 b)) (/ 2 3))) (* -1 (pow a -1) (pow b -1) (pow c -1))) 0)))
(check-sat)
(get-model)
(exit)