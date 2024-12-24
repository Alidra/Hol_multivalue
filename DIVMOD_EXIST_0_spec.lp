require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem155064 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∃ (λ q : El num, (∃ (λ r : El num, ((@COND bool) (= n (NUMERAL _0)) (∧ (= q (NUMERAL _0)) (= r m)) (∧ (= m (+ (* q n) r)) (< r n)))))))))));
