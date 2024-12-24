require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1095389 [A] (h : El A) (t : El (list A)) : Prf (= ((λ t' : El (list A), (= ((@TL A) ((@CONS A) h t')) t')) t) (= ((@TL A) ((@CONS A) h t)) t));
