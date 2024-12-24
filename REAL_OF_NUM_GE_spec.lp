require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1483730 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (real_ge (real_of_num m) (real_of_num n)) (>= m n))))));
