require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2267614 (x : El real) : Prf (= (integer x) (∃ (λ n : El num, (∨ (= x (real_of_num n)) (= x (real_neg (real_of_num n)))))));
