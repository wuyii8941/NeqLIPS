(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (* (/ -153 16) (pow (* (/ 1 4294967296) (pow 2 (/ 25 32)) (pow a 18) (pow b (/ 9 8)) (pow c (/ 153 8))) (pow (+ (* 1 9 (pow 16 -1)) 9) -1))) (* a (pow c 3)) (* b (pow a 3)) (* c (pow b 3)) (* -1 a (pow b 3)) (* -1 b (pow c 3)) (* -1 c (pow a 3)) (* (/ -9 32) (pow 2 (/ 1 2)) (pow a 4)) (* (/ -9 32) (pow 2 (/ 1 2)) (pow b 4)) (* (/ -9 32) (pow 2 (/ 1 2)) (pow c 4)) (* (/ -9 16) (pow 2 (/ 1 2)) (pow a 2) (pow b 2))) 0)))
(check-sat)
(get-model)
(exit)