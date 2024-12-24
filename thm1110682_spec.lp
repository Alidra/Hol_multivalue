require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1110682 [A] (h : El A) (r : El (fun A (fun A bool))) (t : El (list A)) : Prf (= ((λ t' : El (list A), (= ((@PAIRWISE A) r ((@CONS A) h t')) (∧ ((@ALL A) (r h) t') ((@PAIRWISE A) r t')))) t) (= ((@PAIRWISE A) r ((@CONS A) h t)) (∧ ((@ALL A) (r h) t) ((@PAIRWISE A) r t))));
