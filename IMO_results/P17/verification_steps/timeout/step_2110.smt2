(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -1 (pow (+ (* (/ 8273 4) c (pow a 4)) (* (/ 47185 4) c (pow b 2))) -1) (pow (+ (* (/ 8273 4) c (pow a 4)) (* (/ 47185 4) c (pow b 3))) 2)) (* -12160 a (pow c 4)) (* -12160 b (pow a 4)) (* -2432 a (pow b 4)) (* -2432 b (pow c 4)) (* -2240 (pow a 2) (pow c 3)) (* -2240 (pow a 3) (pow b 2)) (* 1600 (pow b 3) (pow c 2)) (* 2240 (pow a 2) (pow b 3)) (* 2240 (pow b 2) (pow c 3)) (* 6080 (pow a 3) (pow c 2)) (* 10752 a b (pow c 3)) (* 12207 a c (pow b 3)) (* 12207 b c (pow a 3)) (* (/ 405 2) c (pow a 2) (pow b 2))) 0)))
(check-sat)
(get-model)
(exit)