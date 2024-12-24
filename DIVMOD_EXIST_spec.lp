require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem154676 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (∃ (λ q : El num, (∃ (λ r : El num, (∧ (= m (+ (* q n) r)) (< r n)))))))))));
