(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -3187671040 a (pow c 4)) (* -3187671040 b (pow a 4)) (* -3092316160 c (pow b 4)) (* -637534208 a (pow b 4)) (* -637534208 b (pow c 4)) (* -587202560 (pow a 2) (pow c 3)) (* -587202560 (pow a 3) (pow b 2)) (* -542179328 c (pow a 4)) (* 419430400 (pow b 3) (pow c 2)) (* 587202560 (pow a 2) (pow b 3)) (* 587202560 (pow b 2) (pow c 3)) (* 1593835520 (pow a 3) (pow c 2)) (* 53084160 c (pow a 2) (pow b 2)) (* 2818572288 a b (pow c 3)) (* 3199991808 a c (pow b 3)) (* 3199991808 b c (pow (+ (/ 2 5) (* (/ 3 5) a)) 5))) 0)))
(check-sat)
(get-model)
(exit)