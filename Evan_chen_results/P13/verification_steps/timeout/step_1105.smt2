(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (* a b c d) 1))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (>= d 0))
(assert (not (<= (+ (* (pow (+ (/ 8 9) b c d (* (/ 1 9) (pow a 3))) -3) (pow (+ (/ 13 18) b c d (* (/ 1 6) a) (* (/ 1 9) (pow a 3))) 4)) (* -1 a (pow d 4)) (* -1 b (pow a 4)) (* -1 c (pow b 4)) (* -1 d (pow c 4))) 0)))
(check-sat)
(get-model)
(exit)