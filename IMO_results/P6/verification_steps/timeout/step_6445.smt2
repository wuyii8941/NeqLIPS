(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -3619524608 (pow b 4)) (* -2776469504 (pow a 4)) (* (pow (+ (* 26638848 (pow (+ a b) 2)) (* 3953770496 b (pow a 3)) (* 12887638016 a (pow b 3))) -1) (pow (+ (* 26638848 (pow (+ a b) 3)) (* 3953770496 b (pow a 3)) (* 12887638016 a (pow b 3))) 2)) (* -7247757312 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -3623878656 (pow a (/ 10 3)) (pow b (/ 2 3)))) 0)))
(check-sat)
(get-model)
(exit)