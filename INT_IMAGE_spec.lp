require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2295400 : Prf (∀ (λ x : El int, (∨ (∃ (λ n : El num, (= x (int_of_num n)))) (∃ (λ n : El num, (= x (int_neg (int_of_num n))))))));
