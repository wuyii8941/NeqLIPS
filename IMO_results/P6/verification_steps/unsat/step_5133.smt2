(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -452440576 (pow b 4)) (* -347058688 (pow a 4)) (* 208116 (pow (+ (* 2 a) (* 2 b)) 4)) (* -1358954496 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 494221312 b (pow a 3)) (* 1610954752 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)