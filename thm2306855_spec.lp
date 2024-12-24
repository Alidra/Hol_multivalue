require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2306855 : Prf (∀ (λ x : El num, (∀ (λ n : El num, (= (int_pow (int_of_num x) n) (int_of_num (EXP x n)))))));
