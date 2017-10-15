(set-logic QF_SLRDI)

(declare-sort Bsth_t 0)

(declare-fun left() (Field Bsth_t Bsth_t))
(declare-fun right() (Field Bsth_t Bsth_t))
(declare-fun data() (Field Bsth_t Rat))

(define-fun bsth ((?E Bsth_t) (?x Rat) (?y Rat) (?F Bsth_t) (?x1 Rat) (?x1 Rat) ) Space
(tospace
    (or
        (and
            (= ?E ?F)
            (= ?x ?x1)
            (= ?y ?x1)
            (tobool emp)
        )

        (exists ((?X Bsth_t) (?Y Bsth_t) (?z Rat) (?x2 Rat) (?y2 Rat))
            (and
                (< ?y2 ?z)
                (< ?z ?x2)
                (tobool
                    (ssep
                        (pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?z)))
                        (bsth ?X ?x ?y2 ?F ?x1 ?x1)
                        (bsth ?Y ?x2 ?y nil ?y ?y)
                    )
                )
            )
        )

        (exists ((?X Bsth_t) (?Y Bsth_t) (?z Rat) (?x2 Rat) (?y2 Rat))
            (and
                (< ?y2 ?z)
                (< ?z ?x2)
                (tobool
                    (ssep
                        (pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?z)))
                        (bsth ?X ?x ?y2 nil ?x ?x)
                        (bsth ?Y ?x2 ?y ?F ?x1 ?x1)
                    )
                )
            )
        )
    )
)
)

(check-sat)