(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 2 (* 2 (pow c 6)) (* 6 (pow a 2)) (* 6 (pow c 2)) (* 6 (pow c 4)) (* 16 (pow a 3)) (* 16 (pow b 3)) (* 6 (pow b 2) (pow c 2)) (* 12 c (pow a 2)) (* 12 c (pow b 2)) (* -4 (+ 3 (pow a 5) (* -1 (pow a 2))) (+ 3 (pow b 5) (* -1 (pow b 2))) (+ 3 (pow c 5) (* -1 (pow c 2)))) (* 24 a b c)) 0)))
(check-sat)
(get-model)
(exit)