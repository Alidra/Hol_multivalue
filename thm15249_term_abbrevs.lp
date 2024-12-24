require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El a1) ≔ ((@COND a0) (= x0 x0));
symbol term1 a0 a1 (x0: El a1) (x1: El a0) ≔ ((@COND a0) (= x0 x0) x1);
symbol term2 a0 a1 (x0: El a1) (x1: El a0) (x2: El a0) ≔ ((@COND a0) (= x0 x0) x1 x2);
symbol term3 a0 a1 (x0: El a1) (x1: El a0) (x2: El a0) ≔ ((@= a0) ((@COND a0) (= x0 x0) x1 x2));
