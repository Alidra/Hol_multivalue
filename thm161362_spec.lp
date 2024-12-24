require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem161362 : Prf (= (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (* n (DIV m n)) (MOD m n)) m))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (* n (DIV m n)) (MOD m n)) m))))));
