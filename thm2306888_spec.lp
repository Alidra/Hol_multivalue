require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2306888 : Prf (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (int_mul (int_of_num m) (int_of_num n)) (int_of_num (* m n))))))) (∀ (λ x : El num, (∀ (λ n : El num, (= (int_pow (int_of_num x) n) (int_of_num (EXP x n))))))));
