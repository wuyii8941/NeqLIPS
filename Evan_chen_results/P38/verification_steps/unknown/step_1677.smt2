(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 88 (* 18 (pow b 3)) (* 24 (pow a 2)) (* 24 (pow c 2)) (* (pow (* (pow 12 (* 2 (pow (+ (pow a 2) (pow c 2) (* a c)) (/ 1 2)))) (pow (+ (pow b 2) (pow c 2) (* b c)) 72)) (pow (+ 144 (pow (+ (pow a 2) (pow c 2) (* a c)) (/ 1 2)) (* 144 (pow (+ (pow a 2) (pow b 2) (* a b)) (/ 1 2)))) -1)) (+ -144 (* -1 (pow (+ (pow a 2) (pow c 2) (* a c)) (/ 1 2))) (* -144 (pow (+ (pow a 2) (pow b 2) (* a b)) (/ 1 2))))) (* 48 a b) (* 48 a c) (* 48 b c)) 0)))
(check-sat)
(get-model)
(exit)