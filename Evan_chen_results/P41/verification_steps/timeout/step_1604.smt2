(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 16 (* 6 (pow c 3)) (* 8 (pow a 9)) (* 9 (pow a 2)) (* 24 (pow b 3)) (* (pow c 3) (+ (/ 9 2) (* (/ 9 2) (pow c 2)))) (* 18 b (pow c 2)) (* 18 c (pow a 2)) (* 18 c (pow b 2)) (* -6 (+ 3 (pow a 5) (* -1 (pow a 2))) (+ 3 (pow b 5) (* -1 (pow b 2))) (+ 3 (pow c 5) (* -1 (pow c 2)))) (* 36 a b c)) 0)))
(check-sat)
(get-model)
(exit)