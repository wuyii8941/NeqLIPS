(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= (+ (pow a 2) (pow b 2) (pow c 2) (pow (+ a b c) 2)) 4))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (not (<= (+ (* -1 (pow a 2)) (* 3 (pow (+ (* (/ 1 2) a) (* (/ 1 2) c)) 4)) (* (/ 3 16) (pow (+ a b) 4)) (* (/ 5 16) (pow (+ b c) 4)) (* -1 a b) (* -1 a c) (* -1 b c) (* -2 (pow b 2) (pow (* (+ 1 (* a b)) (+ 1 (* a c))) (/ 1 2))) (* -2 (pow c 2) (pow (* (+ 1 (* a b)) (+ 1 (* a c))) (/ 1 2))) (* 3 a (pow b 3)) (* 3 a (pow c 3)) (* 3 b (pow c 3)) (* 3 c (pow b 3)) (* -4 b c (pow (* (+ 1 (* a b)) (+ 1 (* a c))) (/ 1 2))) (* 5 b c (pow (+ (/ 2 3) (* (/ 1 3) a)) 6)) (* 8 a b (pow c 2)) (* 8 a c (pow b 2))) 0)))
(check-sat)
(get-model)
(exit)