(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ a b c (* (pow (* (pow a -1) (pow b -1) (pow c 3) (pow (* (pow b -1) (pow c -1)) (pow a 3))) (pow (+ 1 (pow a 3)) -1)) (+ -1 (* -1 (pow a 3)))) (* -1 (pow a -1) (pow b 3) (pow c -1))) 0)))
(check-sat)
(get-model)
(exit)