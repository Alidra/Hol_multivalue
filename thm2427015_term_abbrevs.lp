require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) (x1: El int) (x2: El int) (x3: El int) ≔ ((λ y0 : El int, (= (∧ (¬ (= x0 x1)) (¬ (= x2 y0))) (¬ (= (int_add (int_mul x0 x2) (int_mul x1 y0)) (int_add (int_mul x0 y0) (int_mul x1 x2)))))) x3);
symbol term1 (x0: El int) (x1: El int) (x2: El int) (x3: El int) ≔ (∧ (¬ (= x0 x1)) (¬ (= x2 x3)));
symbol term2 (x0: El int) (x1: El int) (x2: El int) (x3: El int) ≔ (¬ (= (int_add (int_mul x0 x3) (int_mul x2 x1)) (int_add (int_mul x0 x1) (int_mul x2 x3))));
