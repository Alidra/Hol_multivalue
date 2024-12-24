require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5418328 : Prf (= (∀ (λ m : El num, (= (… m (NUMERAL _0)) ((@COND (fun num bool)) (= m (NUMERAL _0)) ((@INSERT num) (NUMERAL _0) (@EMPTY num)) (@EMPTY num))))) (∀ (λ m : El num, (= (… m (NUMERAL _0)) ((@COND (fun num bool)) (= m (NUMERAL _0)) ((@INSERT num) (NUMERAL _0) (@EMPTY num)) (@EMPTY num))))));
