require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El bool) (x1: El a0) (x2: El a0) (x3: El bool) (x4: El a0) (x5: El a0) ≔ (⇒ (= x0 x3) (⇒ (⇒ x3 (= x1 x4)) (⇒ (⇒ (¬ x3) (= x2 x5)) (= ((@COND a0) x0 x1 x2) ((@COND a0) x3 x4 x5)))));
