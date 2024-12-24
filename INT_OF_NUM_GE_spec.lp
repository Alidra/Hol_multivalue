require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2307172 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (int_ge (int_of_num m) (int_of_num n)) (>= m n))))));
