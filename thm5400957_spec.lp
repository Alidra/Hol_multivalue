require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5400957 (m : El num) : Prf (= (∀ (λ x : El num, (= (∧ (<= m x) (<= x (NUMERAL _0))) (= x (NUMERAL _0))))) (∀ (λ x : El num, (= ((@IN num) x (… m (NUMERAL _0))) ((@IN num) x ((@INSERT num) (NUMERAL _0) (@EMPTY num)))))));
