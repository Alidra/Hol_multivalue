require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2330500 : Prf (∀ (λ x : El int, (= (∃ (λ n : El num, (= x (int_of_num n)))) (int_le (int_of_num (NUMERAL _0)) x))));
