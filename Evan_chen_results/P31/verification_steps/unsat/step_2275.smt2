(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -35328 a (pow c 4)) (* -35328 b (pow a 4)) (* -11776 a (pow b 4)) (* -11776 b (pow c 4)) (* -10752 (pow a 2) (pow c 3)) (* -10752 (pow a 3) (pow b 2)) (* 7680 (pow b 3) (pow c 2)) (* 10752 (pow a 2) (pow b 3)) (* 10752 (pow b 2) (pow c 3)) (* 29184 (pow a 3) (pow c 2)) (* (/ -134085 4) c (pow b 4)) (* (/ -39877 4) c (pow a 4)) (* 28672 a b (pow c 3)) (* 35899 a c (pow (+ (/ 2 5) (* (/ 3 5) b)) 5)) (* 35899 b c (pow a 3)) (* (/ 729 2) c (pow a 2) (pow b 2))) 0)))
(check-sat)
(get-model)
(exit)