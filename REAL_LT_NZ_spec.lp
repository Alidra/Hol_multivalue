require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1384523 : Prf (∀ (λ n : El num, (= (¬ (= (real_of_num n) (real_of_num (NUMERAL _0)))) (real_lt (real_of_num (NUMERAL _0)) (real_of_num n)))));
