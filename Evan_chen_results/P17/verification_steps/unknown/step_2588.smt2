(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (* (pow 35 (* (pow a 3) (pow b 2))) (pow (* 35 (pow b 3)) (pow c 2))) (pow (+ (pow c 2) (* (pow a 3) (pow b 2))) -1)) (+ (* -1 (pow c 2)) (* -1 (pow a 3) (pow b 2)))) (* -190 a (pow c 4)) (* -190 b (pow a 4)) (* -190 c (pow b 4)) (* -38 a (pow b 4)) (* -38 b (pow c 4)) (* -38 c (pow a 4)) (* -35 (pow a 2) (pow c 3)) (* 35 (pow a 2) (pow b 3)) (* 35 (pow a 3) (pow c 2)) (* 35 (pow b 2) (pow c 3)) (* 60 a (pow b 2) (pow c 2)) (* 60 b (pow a 2) (pow c 2)) (* 60 c (pow a 2) (pow b 2)) (* 168 a b (pow c 3)) (* 168 a c (pow b 3)) (* 168 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)