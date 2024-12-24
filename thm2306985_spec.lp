require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2306985 (m : El num) : Prf (∀ (λ n : El num, (= (int_max (int_of_num m) (int_of_num n)) (int_of_num (MAX m n)))));
