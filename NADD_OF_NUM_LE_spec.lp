require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1273281 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (nadd_le (nadd_of_num m) (nadd_of_num n)) (<= m n))))));
