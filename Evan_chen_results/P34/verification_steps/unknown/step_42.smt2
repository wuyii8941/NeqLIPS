(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ (pow a 2) (pow b 2) (pow c 2)) 12))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 6 (pow b 3)) (* (pow (* (pow (* 8 b (pow 3 (/ 1 2)) (pow (+ (pow a 2) (pow b 2) (pow c 2)) (/ 1 2))) b) (pow (* 8 c (pow 3 (/ 1 2)) (pow (+ (pow a 2) (pow b 2) (pow c 2)) (/ 1 2))) c)) (pow (+ b c) -1)) (+ (* -1 b) (* -1 c))) (* -8 (pow a 2) (pow (+ (* 3 (pow a 2)) (* 3 (pow b 2)) (* 3 (pow c 2))) (/ 1 2))) (* 6 c (+ (pow a 2) (pow c 2))) (* 12 b (pow c 2)) (* 12 c (pow a 2)) (* 12 c (pow b 2)) (* 18 b (pow a 2))) 0)))
(check-sat)
(get-model)
(exit)