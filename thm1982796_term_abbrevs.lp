require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El real) (x1: El real) ≔ ((λ y0 : El real, (= (real_div x0 y0) (real_mul x0 (real_inv y0)))) x1);
symbol term0 (x0: El real) ≔ ((λ y0 : El real, (∀ (λ y1 : El real, (= (real_div y0 y1) (real_mul y0 (real_inv y1)))))) x0);
symbol term1 (x0: El real) ≔ (∀ (λ y0 : El real, (= (real_div x0 y0) (real_mul x0 (real_inv y0)))));
