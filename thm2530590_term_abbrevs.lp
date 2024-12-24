require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 ≔ (∀ (λ y0 : El int, (∀ (λ y1 : El int, (∀ (λ y2 : El int, (= (rem (rem y0 (int_mul y1 y2)) y2) (rem y0 y2))))))));
symbol term1 (x0: El int) ≔ (∀ (λ y0 : El int, (∀ (λ y1 : El int, (= (rem (rem x0 (int_mul y0 y1)) y1) (rem x0 y1))))));
symbol term0 (x0: El int) (x1: El int) ≔ (∀ (λ y0 : El int, (= (rem (rem x1 (int_mul x0 y0)) y0) (rem x1 y0))));
