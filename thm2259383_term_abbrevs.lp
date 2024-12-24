require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 (x0: El real) ≔ ((@= bool) (∃ (λ y0 : El num, (= (real_abs x0) (real_of_num y0)))));
symbol term0 (x0: El real) ≔ ((λ y0 : El real, (= (integer y0) (∃ (λ y1 : El num, (= (real_abs y0) (real_of_num y1)))))) x0);
symbol term1 (x0: El real) ≔ (∃ (λ y0 : El num, (= (real_abs x0) (real_of_num y0))));
symbol term4 (x0: El real) ≔ (∃ (λ y0 : El num, (∨ (= x0 (real_of_num y0)) (= x0 (real_neg (real_of_num y0))))));
symbol term2 (x0: El real) ≔ ((@= bool) (integer x0));
