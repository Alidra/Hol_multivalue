require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem91144 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (<= (SUC m) n) (< m n))))));
