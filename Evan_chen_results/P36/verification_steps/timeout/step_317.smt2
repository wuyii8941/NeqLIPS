(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> (+ (pow a 2) (pow b 2) (* -1 a b)) 0))
(assert (> (+ (pow b 2) (pow c 2) (* -1 b c)) 0))
(assert (> (+ (pow a 2) (pow c 2) (* -1 a c)) 0))
(assert (not (<= (+ (/ 2 3) (* 3 (pow (+ 6 (* 4 (pow a 2)) (* 4 (pow b 2)) (* 4 (pow c 2)) (* -2 a b) (* -2 a c) (* -2 b c)) (/ 1 2))) (* (pow 3 (/ 1 2)) (pow (+ (* -4 a) (* -4 b) (* -4 c) (* 6 (pow a (/ 1 2)) (pow b (/ 1 2)) (pow c (/ 1 2)))) 3))) 0)))
(check-sat)
(get-model)
(exit)