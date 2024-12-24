require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El num) ≔ (∨ (= x0 (NUMERAL _0)) (¬ (= x0 (NUMERAL _0))));
symbol term0 (x0: El num) ≔ ((λ y0 : El bool, (∨ y0 (¬ y0))) (= x0 (NUMERAL _0)));
