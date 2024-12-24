require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2259383 (x : El real) : Prf (= (= (∃ (λ n : El num, (= (real_abs x) (real_of_num n)))) (∃ (λ n : El num, (∨ (= x (real_of_num n)) (= x (real_neg (real_of_num n))))))) (= (integer x) (∃ (λ n : El num, (∨ (= x (real_of_num n)) (= x (real_neg (real_of_num n))))))));
