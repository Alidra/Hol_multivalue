require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) ≔ ((λ y0 : El real, (∀ (λ y1 : El num, (= (real_pow y0 (SUC y1)) (real_mul y0 (real_pow y0 y1)))))) x0);
