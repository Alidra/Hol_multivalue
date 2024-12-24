require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem161372 : Prf (= (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (* (DIV m n) n) (MOD m n)) m))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (* (DIV m n) n) (MOD m n)) m))))));
