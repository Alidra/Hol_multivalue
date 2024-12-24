require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2307491 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (int_sub (int_of_num m) (int_of_num n)) ((@COND int) (<= n m) (int_of_num (- m n)) (int_neg (int_of_num (- n m)))))))));
