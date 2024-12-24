require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1094867 [A] (t : El (list A)) (h : El A) : Prf (= ((@HD A) ((@CONS A) h t)) h);
