(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (* (pow b (* 5505024 b (pow a 3))) (pow c (* 5135360 (pow a 4)))) (pow (+ (* 5135360 (pow a 4)) (* 5505024 b (pow a 3))) -1)) (+ (* -5135360 (pow a 4)) (* -5505024 b (pow a 3)))) (* -18087936 a (pow c 4)) (* -18087936 b (pow a 4)) (* -17193984 c (pow b 4)) (* -6029312 a (pow b 4)) (* -6029312 b (pow c 4)) (* -5505024 (pow a 2) (pow c 3)) (* 3932160 (pow b 3) (pow c 2)) (* 5505024 (pow a 2) (pow b 3)) (* 5505024 (pow b 2) (pow c 3)) (* 14942208 (pow a 3) (pow c 2)) (* 497664 c (pow a 2) (pow b 2)) (* 14680064 a b (pow c 3)) (* 18255872 a c (pow b 3)) (* 18255872 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)