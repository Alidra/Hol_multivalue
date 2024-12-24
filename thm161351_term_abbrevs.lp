require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El num) (x1: El num) ≔ (+ (* (DIV x0 x1) x1) (MOD x0 x1));
symbol term0 (x0: El num) ≔ (¬ (= x0 (NUMERAL _0)));
