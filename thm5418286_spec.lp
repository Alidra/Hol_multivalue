require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5418286 (m : El num) (h1 : Prf (= m (NUMERAL _0))) : Prf (∀ (λ x : El num, (= (∧ (<= m x) (<= x (NUMERAL _0))) (= x (NUMERAL _0)))));
