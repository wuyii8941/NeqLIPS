(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 1990656 c (pow b 2)) (* 15728640 (pow b 3) (pow c 2)) (* 22020096 (pow a 2) (pow b 3)) (* 22020096 (pow b 2) (pow c 3)) (* 59768832 (pow a 3) (pow c 2))) -1) (pow (+ (* 15728640 (pow b 3) (pow c 2)) (* 22020096 (pow a 2) (pow b 3)) (* 22020096 (pow b 2) (pow c 3)) (* 59768832 (pow a 3) (pow c 2)) (* 1990656 a c (pow b 2))) 2)) (* -72351744 a (pow c 4)) (* -72351744 b (pow a 4)) (* -68775936 c (pow b 4)) (* -24117248 a (pow b 4)) (* -24117248 b (pow c 4)) (* -22020096 (pow a 2) (pow c 3)) (* -22020096 (pow a 3) (pow b 2)) (* -20541440 c (pow a 4)) (* 58720256 a b (pow c 3)) (* 73023488 a c (pow b 3)) (* 73023488 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)