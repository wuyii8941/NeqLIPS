(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 12 (pow c 4)) (* 16 (pow b 6)) (* 32 (pow a 3)) (* (pow (+ 28 (* 8 (pow c 3))) -1) (pow (+ 22 (* 6 (pow a 2)) (* 8 (pow c 3))) 2)) (* 24 b (pow c 2)) (* 24 c (pow a 2)) (* 24 c (pow b 2)) (* -8 (+ 3 (pow a 5) (* -1 (pow a 2))) (+ 3 (pow b 5) (* -1 (pow b 2))) (+ 3 (pow c 5) (* -1 (pow c 2)))) (* 48 a b c)) 0)))
(check-sat)
(get-model)
(exit)