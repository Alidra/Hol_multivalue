require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2841336 (k : El num) : Prf (∀ (λ n : El num, (= (int_of_num (* (NUMERAL k) n)) (int_mul (int_of_num (NUMERAL k)) (int_of_num n)))));
