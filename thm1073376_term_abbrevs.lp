require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El a0) (x1: El a0) (x2: El a1) (x3: El a1) ≔ ((λ y0 : El a1, (= (= ((@̦‚ a0 a1) x0 x2) ((@̦‚ a0 a1) x1 y0)) (∧ (= x0 x1) (= x2 y0)))) x3);
symbol term1 a0 a1 (x0: El a0) (x1: El a0) (x2: El a1) (x3: El a1) ≔ (∧ (= x0 x1) (= x2 x3));
