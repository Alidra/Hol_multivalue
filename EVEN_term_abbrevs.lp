require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 ≔ (EVEN (NUMERAL _0));
symbol term2 ≔ (∧ (= (EVEN (NUMERAL _0)) T) (∀ (λ y0 : El num, (= (EVEN (SUC y0)) (¬ (EVEN y0))))));
symbol term0 ≔ (∀ (λ y0 : El num, (= (EVEN (SUC y0)) (¬ (EVEN y0)))));
