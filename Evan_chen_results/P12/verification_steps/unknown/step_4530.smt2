(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (* (pow (* 512 (pow a 36) (pow c 36) (pow (* 18 (pow c 2)) (* (pow 2 (/ 1 2)) (pow b 2)))) (pow (+ 18 (* (pow 2 (/ 1 2)) (pow b 2))) -1)) (+ -18 (* -1 (pow 2 (/ 1 2)) (pow b 2)))) (* -32 a (pow b 3)) (* -32 b (pow c 3)) (* -32 c (pow a 3)) (* -9 (pow 2 (/ 1 2)) (pow a 4)) (* -9 (pow 2 (/ 1 2)) (pow b 4)) (* -9 (pow 2 (/ 1 2)) (pow c 4)) (* 32 a (pow c 3)) (* 32 b (pow a 3)) (* 32 c (pow b 3)) (* -18 (pow 2 (/ 1 2)) (pow a 2) (pow b 2))) 0)))
(check-sat)
(get-model)
(exit)