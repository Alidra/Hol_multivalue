require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem157261 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (∧ (= m (+ (* (DIV m n) n) (MOD m n))) (< (MOD m n) n)))))));
