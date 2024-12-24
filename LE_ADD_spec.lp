require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem100517 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (<= m (+ m n))))));
