require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El num) ≔ ((λ y0 : El num, (= (SUC (BIT1 y0)) (BIT0 (SUC y0)))) x0);
symbol term0 ≔ (∀ (λ y0 : El num, (= (SUC (BIT1 y0)) (BIT0 (SUC y0)))));
