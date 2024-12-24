require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1098347 [A] (h : El A) (t : El (list A)) : Prf ((λ t' : El (list A), (= ((@LAST A) ((@CONS A) h t')) ((@COND A) (= t' (@NIL A)) h ((@LAST A) t')))) t);
