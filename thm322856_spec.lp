require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem322856 (t1 : El bool) (t2 : El bool) (t3 : El bool) : Prf (= (∨ (∨ t1 t2) t3) (∨ t1 (∨ t2 t3)));
