require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem199825 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (= (DIV m n) m) (∨ (= m (NUMERAL _0)) (= n (NUMERAL (BIT1 _0)))))))));
