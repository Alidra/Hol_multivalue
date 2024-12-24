require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1111624 [A] (h : El A) (k : El A) (t : El (list A)) : Prf (∧ (= ((@LAST A) ((@CONS A) h (@NIL A))) h) (= ((@LAST A) ((@CONS A) h ((@CONS A) k t))) ((@LAST A) ((@CONS A) k t))));
