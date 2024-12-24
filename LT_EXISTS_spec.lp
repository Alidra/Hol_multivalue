require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem100361 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (< m n) (∃ (λ d : El num, (= n (+ m (SUC d))))))))));
