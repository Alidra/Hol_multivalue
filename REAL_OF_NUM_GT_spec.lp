require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1483793 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (real_gt (real_of_num m) (real_of_num n)) (> m n))))));
