(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -43248768 (pow b 4)) (* -33369216 (pow a 4)) (* 832464 (pow (+ a b) 4)) (* -84934656 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -42467328 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 6935148993280985146589184 (pow a 3) (pow b 3) (pow (+ (* 43003392 b) (* 147697152 a)) -2))) 0)))
(check-sat)
(get-model)
(exit)