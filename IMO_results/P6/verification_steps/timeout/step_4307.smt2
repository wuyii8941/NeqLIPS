(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -28832512 (pow b 4)) (* -22246144 (pow a 4)) (* (pow (+ (* 554976 (pow a 4)) (* 554976 (pow b 2)) (* 3329856 (pow a 2) (pow b 2)) (* 30888832 b (pow a 3)) (* 100684672 a (pow b 3))) -1) (pow (+ (* 554976 (pow a 4)) (* 554976 (pow b 3)) (* 3329856 (pow a 2) (pow b 2)) (* 30888832 b (pow a 3)) (* 100684672 a (pow b 3))) 2)) (* -56623104 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -28311552 (pow a (/ 10 3)) (pow b (/ 2 3)))) 0)))
(check-sat)
(get-model)
(exit)