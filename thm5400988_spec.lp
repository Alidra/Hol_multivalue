require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5400988 (m : El num) : Prf (= (∀ (λ x : El num, (¬ (∧ (<= m x) (<= x (NUMERAL _0)))))) (∀ (λ x : El num, (= ((@IN num) x (… m (NUMERAL _0))) ((@IN num) x (@EMPTY num))))));
