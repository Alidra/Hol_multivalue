require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2841270 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (<= m n) (int_le (int_of_num m) (int_of_num n)))))));
