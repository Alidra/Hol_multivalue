require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem231346 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (MOD m (* n p)) (+ (* n (MOD (DIV m n) p)) (MOD m n)))))))));
