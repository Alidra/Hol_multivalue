require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2306952 (m : El num) : Prf (∀ (λ n : El num, (= (int_min (int_of_num m) (int_of_num n)) (int_of_num (MIN m n)))));
