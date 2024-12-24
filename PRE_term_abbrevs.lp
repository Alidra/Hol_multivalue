require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El num, (= (PRE (SUC y0)) y0)));
symbol term2 ≔ (∧ (= (PRE (NUMERAL _0)) (NUMERAL _0)) (∀ (λ y0 : El num, (= (PRE (SUC y0)) y0))));
symbol term1 ≔ (PRE (NUMERAL _0));
