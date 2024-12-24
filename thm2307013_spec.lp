require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2307013 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (int_lt (int_of_num m) (int_of_num n)) (< m n))))));
