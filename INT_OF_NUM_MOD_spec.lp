require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2307350 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (int_of_num (MOD m n)) (int_sub (int_of_num m) (int_mul (int_of_num (DIV m n)) (int_of_num n))))))));
