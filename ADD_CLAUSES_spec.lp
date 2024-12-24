require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem77629 : Prf (∧ (∀ (λ n : El num, (= (+ (NUMERAL _0) n) n))) (∧ (∀ (λ m : El num, (= (+ m (NUMERAL _0)) m))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (SUC m) n) (SUC (+ m n))))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (+ m (SUC n)) (SUC (+ m n))))))))));
