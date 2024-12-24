require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) (x1: El int) ≔ (∀ (λ y0 : El int, (= (rem (rem x0 (int_mul x1 y0)) x1) (rem x0 x1))));
symbol term1 (x0: El int) ≔ (∀ (λ y0 : El int, (∀ (λ y1 : El int, (= (rem (rem x0 (int_mul y0 y1)) y0) (rem x0 y0))))));
