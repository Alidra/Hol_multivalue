require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1669963 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (real_of_num (MOD m n)) (real_sub (real_of_num m) (real_mul (real_of_num (DIV m n)) (real_of_num n))))))));
