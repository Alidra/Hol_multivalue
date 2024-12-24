require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El bool) ≔ (⇒ (¬ x0) F);
symbol term1 ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (< (MOD y0 y1) y1) (¬ (= y1 (NUMERAL _0))))))));
symbol term2 ≔ (⇒ (¬ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (< (MOD y0 y1) y1) (¬ (= y1 (NUMERAL _0))))))))) F);
