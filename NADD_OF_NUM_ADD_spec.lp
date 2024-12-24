require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1276280 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (nadd_eq (nadd_add (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (+ m n)))))));
