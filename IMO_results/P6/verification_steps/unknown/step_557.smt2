(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 208116 (pow a 4)) (* 208116 (pow b 4)) (* (pow (* (pow a (* 16684608 (pow a 2))) (pow b (* 21624384 (pow b 2)))) (pow (+ (* 8342304 (pow a 2)) (* 10812192 (pow b 2))) -1)) (+ (* -10812192 (pow b 2)) (* -8342304 (pow a 2)))) (* -21233664 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -10616832 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 1248696 (pow a 2) (pow b 2)) (* 11583312 b (pow a 3)) (* 37756752 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)