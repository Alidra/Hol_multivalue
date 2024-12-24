require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El a1) (x1: El (prod a1 a0)) (x2: El (type1641 a0 a1)) ≔ ((@ASSOC a0 a1) x0 ((@CONS (prod a1 a0)) x1 x2));
symbol term1 a0 a1 (x0: El (prod a1 a0)) (x1: El a1) (x2: El (type1641 a0 a1)) ≔ ((@COND a0) (= ((@FST a1 a0) x0) x1) ((@SND a1 a0) x0) ((@ASSOC a0 a1) x1 x2));
