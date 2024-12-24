require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1670410 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (real_of_num (DIV m n)) (real_sub (real_div (real_of_num m) (real_of_num n)) (real_div (real_of_num (MOD m n)) (real_of_num n))))))));
