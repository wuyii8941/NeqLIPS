(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -36175872 a (pow c 4)) (* -36175872 b (pow a 4)) (* -34325760 c (pow b 4)) (* -12058624 a (pow b 4)) (* -12058624 b (pow c 4)) (* -11010048 (pow a 2) (pow c 3)) (* -11010048 (pow a 3) (pow b 2)) (* -10208512 c (pow a 4)) (* 7864320 (pow b 3) (pow c 2)) (* 11010048 (pow a 2) (pow b 3)) (* 11010048 (pow b 2) (pow c 3)) (* 29884416 (pow a 3) (pow c 2)) (* 373248 c (pow a 2) (pow b 2)) (* 29360128 a b (pow c 3)) (* 36760576 a c (pow b 3)) (* 36760576 b c (pow (+ (/ 2 5) (* (/ 3 5) a)) 5))) 0)))
(check-sat)
(get-model)
(exit)