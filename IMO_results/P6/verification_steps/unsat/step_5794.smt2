(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -3592885760 (pow b 4)) (* -2749830656 (pow a 4)) (* -7247757312 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -3623878656 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 159833088 (pow a 2) (pow b 2)) (* 4960419981718080832473804046336 (pow a 3) (pow b 3) (pow (+ (* 4060325888 b) (* 12994193408 a)) -2))) 0)))
(check-sat)
(get-model)
(exit)