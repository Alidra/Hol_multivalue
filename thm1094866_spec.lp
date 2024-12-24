require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1094866 [A] (t : El (list A)) (h : El A) : Prf (= ((λ h' : El A, (= ((@HD A) ((@CONS A) h' t)) h')) h) (= ((@HD A) ((@CONS A) h t)) h));
