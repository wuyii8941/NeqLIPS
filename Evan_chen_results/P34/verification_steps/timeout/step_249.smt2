(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ (pow a 2) (pow b 2) (pow c 2)) 12))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 12 (pow b 3)) (* 12 (pow c 3)) (* -1 (pow (+ (* 8 (pow (+ (pow a 2) (pow b 2) (pow c 2)) (/ 1 2)) (+ (pow b 2) (pow c 2) (* 2 b c))) (* 16 (pow 3 (/ 1 2)) (pow a 2))) (/ 1 2)) (pow (+ (* 24 (pow (+ (pow a 2) (pow b 2) (pow c 2)) (/ 1 2)) (+ (pow b 2) (pow c 2) (* 2 b c))) (* 16 (pow 3 (/ 1 2)) (pow a 2) (+ (pow a 2) (pow b 2) (pow c 2)))) (pow 2 -1))) (* 24 b (pow c 2)) (* 24 c (pow b 2)) (* 36 b (pow a 2)) (* 36 c (pow a 2))) 0)))
(check-sat)
(get-model)
(exit)