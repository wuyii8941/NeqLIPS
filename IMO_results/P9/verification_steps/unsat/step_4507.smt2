(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ -8 (* (pow (+ (pow (+ (pow a 2) (pow c 2) (* 2 (pow b 2)) (* 2 a c)) -1) (* 2 (pow (+ (pow b 2) (pow c 2) (* 2 (pow a 2)) (* 2 b c)) -1)) (* (pow (+ a b (* 2 c)) 2) (pow (+ (pow a 2) (pow b 2) (* 2 (pow c 2)) (* 2 a b)) -1)) (* 2 (pow b 2) (pow (+ (pow b 2) (pow c 2) (* 2 (pow a 2)) (* 2 b c)) -1))) -1) (pow (+ (* (pow (+ a b (* 2 c)) 2) (pow (+ (pow a 2) (pow b 2) (* 2 (pow c 2)) (* 2 a b)) -1)) (* (pow (+ (pow a 2) (pow c 2) (* 2 (pow b 2)) (* 2 a c)) -1) (+ a c (* 2 b))) (* 2 c (pow (+ (pow b 2) (pow c 2) (* 2 (pow a 2)) (* 2 b c)) -1)) (* 2 (pow b 2) (pow (+ (pow b 2) (pow c 2) (* 2 (pow a 2)) (* 2 b c)) -1))) 2)) (* 8 (pow a 2) (pow (+ (pow b 2) (pow c 2) (* 2 (pow a 2)) (* 2 b c)) -1)) (* 4 b c (pow (+ (pow b 2) (pow c 2) (* 2 (pow a 2)) (* 2 b c)) -1))) 0)))
(check-sat)
(get-model)
(exit)