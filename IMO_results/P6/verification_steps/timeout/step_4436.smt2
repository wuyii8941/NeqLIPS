(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -675762 (pow b 4)) (* -521394 (pow a 4)) (* (pow (+ (* (/ 52029 16) (pow (+ (* 2 a) (* 2 b)) 2)) (* 671928 b (pow a 3)) (* 2307768 a (pow b 3))) 2) (pow (+ (* 671928 b (pow a 3)) (* 2307768 a (pow b 3)) (* 208116 1 1 (pow (* 4 4) -1))) -1)) (* -1327104 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -663552 (pow a (/ 10 3)) (pow b (/ 2 3)))) 0)))
(check-sat)
(get-model)
(exit)