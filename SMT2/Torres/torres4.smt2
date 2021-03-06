(set-option :produce-models true)
(set-logic QF_LIA)
(declare-fun torre_0 () Int)
(declare-fun torre_1 () Int)
(declare-fun torre_2 () Int)
(declare-fun torre_3 () Int)
(declare-fun torre_4 () Int)
(declare-fun torre_5 () Int)
(assert (<= 0 torre_0 ) )
(assert (<= torre_0 2 ) )
(assert (<= 0 torre_1 ) )
(assert (<= torre_1 2 ) )
(assert (<= 0 torre_2 ) )
(assert (<= torre_2 2 ) )
(assert (<= 0 torre_3 ) )
(assert (<= torre_3 2 ) )
(assert (<= 0 torre_4 ) )
(assert (<= torre_4 2 ) )
(assert (<= 0 torre_5 ) )
(assert (<= torre_5 2 ) )
(assert (or (not (= torre_0 2 ) ) (not (= torre_1 2 ) ) ) )
(assert (or (not (= torre_1 2 ) ) (not (= torre_2 2 ) ) ) )
(assert (or (not (= torre_2 2 ) ) (not (= torre_3 2 ) ) ) )
(assert (or (not (= torre_3 2 ) ) (not (= torre_4 2 ) ) ) )
(assert (or (not (= torre_4 2 ) ) (not (= torre_5 2 ) ) ) )
(assert (>= (ite (= torre_0 0 ) 1 0 ) (ite (= torre_0 2 ) 1 0 ) ) )
(assert (>= (+ (ite (= torre_1 0 ) 1 0 ) (ite (= torre_0 0 ) 1 0 ) ) (+ (ite (= torre_1 2 ) 1 0 ) (ite (= torre_0 2 ) 1 0 ) ) ) )
(assert (>= (+ (ite (= torre_2 0 ) 1 0 ) (+ (ite (= torre_1 0 ) 1 0 ) (ite (= torre_0 0 ) 1 0 ) ) ) (+ (ite (= torre_2 2 ) 1 0 ) (+ (ite (= torre_1 2 ) 1 0 ) (ite (= torre_0 2 ) 1 0 ) ) ) ) )
(assert (>= (+ (ite (= torre_3 0 ) 1 0 ) (+ (ite (= torre_2 0 ) 1 0 ) (+ (ite (= torre_1 0 ) 1 0 ) (ite (= torre_0 0 ) 1 0 ) ) ) ) (+ (ite (= torre_3 2 ) 1 0 ) (+ (ite (= torre_2 2 ) 1 0 ) (+ (ite (= torre_1 2 ) 1 0 ) (ite (= torre_0 2 ) 1 0 ) ) ) ) ) )
(assert (>= (+ (ite (= torre_4 0 ) 1 0 ) (+ (ite (= torre_3 0 ) 1 0 ) (+ (ite (= torre_2 0 ) 1 0 ) (+ (ite (= torre_1 0 ) 1 0 ) (ite (= torre_0 0 ) 1 0 ) ) ) ) ) (+ (ite (= torre_4 2 ) 1 0 ) (+ (ite (= torre_3 2 ) 1 0 ) (+ (ite (= torre_2 2 ) 1 0 ) (+ (ite (= torre_1 2 ) 1 0 ) (ite (= torre_0 2 ) 1 0 ) ) ) ) ) ) )
(assert (>= (+ (ite (= torre_5 0 ) 1 0 ) (+ (ite (= torre_4 0 ) 1 0 ) (+ (ite (= torre_3 0 ) 1 0 ) (+ (ite (= torre_2 0 ) 1 0 ) (+ (ite (= torre_1 0 ) 1 0 ) (ite (= torre_0 0 ) 1 0 ) ) ) ) ) ) (+ (ite (= torre_5 2 ) 1 0 ) (+ (ite (= torre_4 2 ) 1 0 ) (+ (ite (= torre_3 2 ) 1 0 ) (+ (ite (= torre_2 2 ) 1 0 ) (+ (ite (= torre_1 2 ) 1 0 ) (ite (= torre_0 2 ) 1 0 ) ) ) ) ) ) ) )
(assert (<= (+ (ite (= torre_5 0 ) 1 0 ) (+ (ite (= torre_4 0 ) 1 0 ) (+ (ite (= torre_3 0 ) 1 0 ) (+ (ite (= torre_2 0 ) 1 0 ) (+ (ite (= torre_1 0 ) 1 0 ) (ite (= torre_0 0 ) 1 0 ) ) ) ) ) ) 2 ) )
(assert (<= (+ (ite (= torre_5 1 ) 1 0 ) (+ (ite (= torre_4 1 ) 1 0 ) (+ (ite (= torre_3 1 ) 1 0 ) (+ (ite (= torre_2 1 ) 1 0 ) (+ (ite (= torre_1 1 ) 1 0 ) (ite (= torre_0 1 ) 1 0 ) ) ) ) ) ) 3 ) )
(assert (<= (+ (ite (= torre_5 2 ) 1 0 ) (+ (ite (= torre_4 2 ) 1 0 ) (+ (ite (= torre_3 2 ) 1 0 ) (+ (ite (= torre_2 2 ) 1 0 ) (+ (ite (= torre_1 2 ) 1 0 ) (ite (= torre_0 2 ) 1 0 ) ) ) ) ) ) 2 ) )
(assert (<= (+ (ite (not (= torre_5 1 ) ) 1 0 ) (+ (ite (not (= torre_4 1 ) ) 1 0 ) (+ (ite (not (= torre_3 1 ) ) 1 0 ) (+ (ite (not (= torre_2 1 ) ) 1 0 ) (+ (ite (not (= torre_1 1 ) ) 1 0 ) (ite (not (= torre_0 1 ) ) 1 0 ) ) ) ) ) ) 3 ) )
(assert (= torre_0 1 ) )
(check-sat)
(get-value (torre_5) )
(get-value (torre_4) )
(get-value (torre_3) )
(get-value (torre_2) )
(get-value (torre_1) )
(get-value (torre_0) )
