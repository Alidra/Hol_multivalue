require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem161368 (m : El num) : Prf (∀ (λ n : El num, (= (+ (* (DIV m n) n) (MOD m n)) m)));
