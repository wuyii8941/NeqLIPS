(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (* a b c d) 1))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (>= d 0))
(assert (not (<= (+ (/ 1 2) b c d (* (/ 1 2) (pow a 2)) (* (pow c (* (pow (+ d (pow b 4) (* b (pow a 4))) -1) (+ (pow b 4) (* 4 d)))) (+ (* -1 d) (* -1 (pow b 4)) (* -1 b (pow a 4)))) (* -1 a (pow d 4))) 0)))
(check-sat)
(get-model)
(exit)