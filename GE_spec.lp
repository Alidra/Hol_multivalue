require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem90226 : Prf (∀ (λ n : El num, (∀ (λ m : El num, (= (>= m n) (<= n m))))));
