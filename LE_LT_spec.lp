require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem97338 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (<= m n) (∨ (< m n) (= m n)))))));
