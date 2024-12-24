require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El num, (= (… y0 (NUMERAL _0)) ((@COND (fun num bool)) (= y0 (NUMERAL _0)) ((@INSERT num) (NUMERAL _0) (@EMPTY num)) (@EMPTY num)))));
