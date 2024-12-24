require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) ≔ ((λ y0 : El num, (= (+ (BIT1 y0) _0) (BIT1 y0))) x0);
symbol term1 (x0: El num) ≔ (+ (BIT1 x0) _0);
