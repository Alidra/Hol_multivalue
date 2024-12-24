require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2837524 : Prf (∀ (λ n : El num, (∀ (λ x : El num, (∀ (λ y : El num, (= (num_mod n x y) (int_mod (int_of_num n) (int_of_num x) (int_of_num y)))))))));
