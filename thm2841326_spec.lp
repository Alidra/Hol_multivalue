require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2841326 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (int_of_num (+ m n)) (int_add (int_of_num m) (int_of_num n)))))));
