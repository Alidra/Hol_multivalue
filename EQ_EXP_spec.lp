require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem150395 : Prf (∀ (λ x : El num, (∀ (λ m : El num, (∀ (λ n : El num, (= (= (EXP x m) (EXP x n)) ((@COND bool) (= x (NUMERAL _0)) (= (= m (NUMERAL _0)) (= n (NUMERAL _0))) (∨ (= x (NUMERAL (BIT1 _0))) (= m n))))))))));
