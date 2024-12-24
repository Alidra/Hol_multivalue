require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1340396 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (real_mul (real_of_num m) (real_of_num n)) (real_of_num (* m n)))))));
