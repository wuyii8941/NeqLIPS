(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -710448 (pow b 4)) (* -556080 (pow a 4)) (* (pow (+ (* 34686 (pow a 4)) (* 34686 (pow b 2)) (* 208116 (pow a 2))) -1) (pow (+ (* 34686 (pow a 4)) (* 34686 (pow b 3)) (* 208116 b (pow a 2))) 2)) (* -1327104 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -663552 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 671928 b (pow a 3)) (* 2307768 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)