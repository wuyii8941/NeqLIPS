(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (not (<= (+ (* -1 (pow a 6)) (* -1 (pow b 6)) (* -1 (pow c 6)) (* (pow (* (pow a 12) (pow b 12) (pow c 12)) (pow (+ 6 (* 3 (pow b 2) (pow c 4))) -1)) (+ -6 (* -3 (pow b 2) (pow c 4)))) (* -3 (pow a 2) (pow b 4)) (* -3 (pow a 2) (pow c 4)) (* -3 (pow a 4) (pow b 2)) (* 21 (pow a 2) (pow b 2) (pow c 2))) 0)))
(check-sat)
(get-model)
(exit)