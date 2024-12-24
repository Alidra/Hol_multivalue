require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (∀ (λ y2 : El num, (⇒ (¬ (= y0 (NUMERAL _0))) (= (MOD (EXP y0 y1) (EXP y0 y2)) ((@COND num) (∨ (<= y2 y1) (= y0 (NUMERAL (BIT1 _0)))) (NUMERAL _0) (EXP y0 y1))))))))));
