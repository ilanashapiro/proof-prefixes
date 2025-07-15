(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)

; Simple clauses:
(assert (or a b))
(assert (or (not a) c))
(assert (or (not b) (not c)))
(check-sat)