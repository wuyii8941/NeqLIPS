(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -2 a (pow b 8)) (* -2 b (pow c 8)) (* -2 c (pow a 8)) (* 2 (pow a 5) (pow b 2) (pow c 2)) (* a b (pow (+ (/ 4 9) (* (/ 5 9) c)) 9) (+ (pow a 2) (pow b 2))) (* a c (pow b 5) (+ (pow a 2) (pow c 2)))) 0)))
(check-sat)
(get-model)
(exit)