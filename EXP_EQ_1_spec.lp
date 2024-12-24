require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem87287 : Prf (∀ (λ x : El num, (∀ (λ n : El num, (= (= (EXP x n) (NUMERAL (BIT1 _0))) (∨ (= x (NUMERAL (BIT1 _0))) (= n (NUMERAL _0))))))));
