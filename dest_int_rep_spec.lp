require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2267790 : Prf (∀ (λ i : El int, (∃ (λ n : El num, (∨ (= (real_of_int i) (real_of_num n)) (= (real_of_int i) (real_neg (real_of_num n))))))));
