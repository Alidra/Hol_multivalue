require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1110684 [A] (h : El A) (r : El (fun A (fun A bool))) (t : El (list A)) : Prf (∧ (= ((@PAIRWISE A) r (@NIL A)) T) (= ((@PAIRWISE A) r ((@CONS A) h t)) (∧ ((@ALL A) (r h) t) ((@PAIRWISE A) r t))));
