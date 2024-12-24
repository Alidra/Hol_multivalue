require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5405853 (m : El num) : Prf (⇒ (¬ (= m (NUMERAL _0))) (∀ (λ x : El num, (¬ (∧ (<= m x) (<= x (NUMERAL _0)))))));
