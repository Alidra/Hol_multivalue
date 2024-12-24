require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2837601 : Prf (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ n : El num, (= ((@== num) x y (num_mod n)) ((@== int) (int_of_num x) (int_of_num y) (int_mod (int_of_num n))))))))));
