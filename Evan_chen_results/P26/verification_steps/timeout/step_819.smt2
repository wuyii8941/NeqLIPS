(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ -3 4) (* 27 a (pow (+ (* 162 (pow a 2)) (* 18 (pow 3 (/ 1 2)) (pow (+ (pow a 4) (* a (pow b 3)) (* a (pow c 3)) (* 3 b (pow a 3)) (* 3 c (pow a 3)) (* 3 (pow a 2) (pow b 2)) (* 3 (pow a 2) (pow c 2)) (* 3 a b (pow c 2)) (* 3 a c (pow b 2)) (* 6 b c (pow a 2))) (/ 1 2)))) -1) (+ a b c)) (* 27 b (pow (+ (* 198 (pow b 2)) (* 36 a c) (* 45 a b) (* 45 b c)) -1) (+ a b c)) (* 27 c (pow (+ (* 9 (pow a 2)) (* 9 (pow b 2)) (* 198 (pow c 2)) (* 18 a b) (* 45 a c) (* 45 b c)) -1) (+ a b c))) 0)))
(check-sat)
(get-model)
(exit)