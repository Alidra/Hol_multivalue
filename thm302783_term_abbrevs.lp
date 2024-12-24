require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) ≔ (SUC (+ x0 x0));
symbol term1 (x0: El num) ≔ (+ (* (NUMERAL (BIT0 (BIT1 _0))) x0) (NUMERAL (BIT1 _0)));
