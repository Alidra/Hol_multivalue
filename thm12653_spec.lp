require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem12653 [A] (t1 : El A) (t2 : El A) : Prf (∧ (= ((@COND A) T t1 t2) t1) (= ((@COND A) F t1 t2) t2));
