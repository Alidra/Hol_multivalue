require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3183066 [_83031] (P : El bool) (v : El _83031) (t : El _83031) : Prf (= ((λ t' : El _83031, (= ((@SETSPEC _83031) v P t') (∧ P (= v t')))) t) (= ((@SETSPEC _83031) v P t) (∧ P (= v t))));
