require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1300973 : Prf (∀ (λ x : El nadd, (= (nadd_rinv x) (λ n : El num, (DIV (* n n) (dest_nadd x n))))));
