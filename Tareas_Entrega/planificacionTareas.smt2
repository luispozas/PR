(set-option :produce-models true)
(set-logic QF_LIA)
(declare-fun tarea_0 () Int)
(declare-fun tarea_1 () Int)
(declare-fun tarea_2 () Int)
(declare-fun tarea_3 () Int)
(declare-fun tarea_4 () Int)
(declare-fun tarea_5 () Int)
(assert (<= 1 tarea_0 ) )
(assert (<= tarea_0 20 ) )
(assert (<= 1 tarea_1 ) )
(assert (<= tarea_1 20 ) )
(assert (<= 1 tarea_2 ) )
(assert (<= tarea_2 20 ) )
(assert (<= 1 tarea_3 ) )
(assert (<= tarea_3 20 ) )
(assert (<= 1 tarea_4 ) )
(assert (<= tarea_4 20 ) )
(assert (<= 1 tarea_5 ) )
(assert (<= tarea_5 20 ) )
(assert (<= 3 8 ) )
(assert (<= 8 8 ) )
(assert (<= 8 8 ) )
(assert (<= 6 8 ) )
(assert (<= 3 8 ) )
(assert (<= 4 8 ) )
(assert (< (+ tarea_0 3 ) 20 ) )
(assert (< (+ tarea_1 8 ) 20 ) )
(assert (< (+ tarea_2 8 ) 20 ) )
(assert (< (+ tarea_3 6 ) 20 ) )
(assert (< (+ tarea_4 3 ) 20 ) )
(assert (< (+ tarea_5 4 ) 20 ) )
(assert (<= (+ tarea_3 6 ) tarea_2 ) )
(assert (<= (+ tarea_4 3 ) tarea_2 ) )
(assert (<= (+ tarea_0 3 ) tarea_4 ) )
(assert (<= (+ tarea_0 3 ) tarea_5 ) )
(check-sat)
(get-value (tarea_0) )
(get-value (tarea_1) )
(get-value (tarea_2) )
(get-value (tarea_3) )
(get-value (tarea_4) )
(get-value (tarea_5) )