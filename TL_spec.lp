require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1095390 [A] (h : El A) (t : El (list A)) : Prf (= ((@TL A) ((@CONS A) h t)) t);
