require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem90708 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (MAX m n) ((@COND num) (<= m n) n m))))));
