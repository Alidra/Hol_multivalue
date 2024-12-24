require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5418290 (m : El num) (h1 : Prf (= m (NUMERAL _0))) : Prf (∀ (λ x : El num, (= ((@IN num) x (… m (NUMERAL _0))) ((@IN num) x ((@INSERT num) (NUMERAL _0) (@EMPTY num))))));
