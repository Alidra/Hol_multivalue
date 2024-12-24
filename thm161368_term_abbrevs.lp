require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) ≔ (∀ (λ y0 : El num, (= (+ (* (DIV x0 y0) y0) (MOD x0 y0)) x0)));
