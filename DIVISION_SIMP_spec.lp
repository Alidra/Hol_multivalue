require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem161374 : Prf (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (* (DIV m n) n) (MOD m n)) m))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (* n (DIV m n)) (MOD m n)) m))))));
