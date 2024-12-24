require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) ≔ (* (NUMERAL (BIT0 (BIT1 _0))) x0);
symbol term2 (x0: El num) ≔ ((@= num) (* (NUMERAL (BIT0 (BIT1 _0))) x0));
symbol term1 (x0: El num) ≔ ((@= num) (+ x0 x0));
symbol term3 (x0: El num) (x1: El num) ≔ ((@= bool) (= x0 x1));
