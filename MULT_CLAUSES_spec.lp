require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem81645 : Prf (∧ (∀ (λ n : El num, (= (* (NUMERAL _0) n) (NUMERAL _0)))) (∧ (∀ (λ m : El num, (= (* m (NUMERAL _0)) (NUMERAL _0)))) (∧ (∀ (λ n : El num, (= (* (NUMERAL (BIT1 _0)) n) n))) (∧ (∀ (λ m : El num, (= (* m (NUMERAL (BIT1 _0))) m))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (* (SUC m) n) (+ (* m n) n)))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (* m (SUC n)) (+ m (* m n))))))))))));
