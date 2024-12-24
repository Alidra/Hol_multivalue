require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2841350 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (int_of_num (MAX m n)) (int_max (int_of_num m) (int_of_num n)))))));
