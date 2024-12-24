require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) (x1: El int) (x2: El int) ≔ ((λ y0 : El int, (= ((@== int) x0 x1 (int_mod y0)) (∃ (λ y1 : El int, (= (int_sub x0 x1) (int_mul y0 y1)))))) x2);
symbol term2 (x0: El int) (x1: El int) (x2: El int) ≔ (∃ (λ y0 : El int, (= (int_sub x0 x1) (int_mul x2 y0))));
symbol term1 (x0: El int) (x1: El int) (x2: El int) ≔ ((@== int) x0 x1 (int_mod x2));
