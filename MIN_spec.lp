require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem90961 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (MIN m n) ((@COND num) (<= m n) m n))))));
