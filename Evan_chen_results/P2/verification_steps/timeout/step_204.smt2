(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (+ a b c d) 4))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> d 0))
(assert (not (<= (+ (pow (* (+ 1 (pow c 2) (* (pow a 2) (pow b 2))) (+ 4 (* 4 (pow a 2)) (* 4 (pow a 2) (pow d 2)))) (/ 1 2)) (* -3 (pow a 2)) (* -3 (pow b 2)) (* -3 (pow c 2)) (* -3 (pow d 2)) (* 2 b c) (* 2 b d) (* 2 c d)) 0)))
(check-sat)
(get-model)
(exit)