(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (+ a b c d) 4))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> d 0))
(assert (not (<= (+ 1 (* -2 (pow (+ (* 2 a d (pow (+ (pow a 3) (* 63 b c d)) (/ -1 3)) (pow (+ (pow d 3) (* 63 a b c)) (/ -1 3))) (* 2 b c (pow (+ (pow b 3) (* 63 a c d)) (/ -1 3)) (pow (+ (pow c 3) (* 63 a b d)) (/ -1 3)))) (pow 2 -1)))) 0)))
(check-sat)
(get-model)
(exit)