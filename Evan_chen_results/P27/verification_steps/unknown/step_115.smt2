(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (+ a b c d) 4))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> d 0))
(assert (not (<= (+ (pow a 2) (pow b 2) (pow c 2) (pow d 2) (* (/ -1 256) (pow a -2) (pow (+ a b c d) 4)) (* (/ -1 256) (pow b -2) (pow (+ a b c d) 4)) (* (/ -1 256) (pow c -2) (pow (+ a b c d) 4)) (* (pow c (pow (+ 1 a b d) -1)) (pow d -2) (pow (+ a b c d) 3) (+ (/ -1 256) (* (/ -1 256) a) (* (/ -1 256) b) (* (/ -1 256) d)))) 0)))
(check-sat)
(get-model)
(exit)