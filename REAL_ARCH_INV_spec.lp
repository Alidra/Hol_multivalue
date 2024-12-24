require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1703820 : Prf (∀ (λ e : El real, (= (real_lt (real_of_num (NUMERAL _0)) e) (∃ (λ n : El num, (∧ (¬ (= n (NUMERAL _0))) (∧ (real_lt (real_of_num (NUMERAL _0)) (real_inv (real_of_num n))) (real_lt (real_inv (real_of_num n)) e))))))));
