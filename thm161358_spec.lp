require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem161358 (m : El num) : Prf (∀ (λ n : El num, (= (+ (* n (DIV m n)) (MOD m n)) m)));
