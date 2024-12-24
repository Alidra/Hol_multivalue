require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 ≔ (∧ (= (ODD (NUMERAL _0)) F) (∀ (λ y0 : El num, (= (ODD (SUC y0)) (¬ (ODD y0))))));
symbol term0 ≔ (∀ (λ y0 : El num, (= (ODD (SUC y0)) (¬ (ODD y0)))));
symbol term1 ≔ (ODD (NUMERAL _0));
