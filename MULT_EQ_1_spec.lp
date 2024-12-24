require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem85714 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (= (* m n) (NUMERAL (BIT1 _0))) (∧ (= m (NUMERAL (BIT1 _0))) (= n (NUMERAL (BIT1 _0)))))))));
