(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -1809762304 (pow b 4)) (* -1388234752 (pow a 4)) (* -3623878656 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -1811939328 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 1664928 (pow (+ (* 2 a) (* 2 b)) 3) (pow (+ (* 2 (pow a 2)) (* 2 (pow b 2))) (/ 1 2))) (* 1976885248 b (pow a 3)) (* 6443819008 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)