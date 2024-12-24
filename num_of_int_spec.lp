require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2833930 : Prf (∀ (λ x : El int, (= (num_of_int x) ((@ε num) (λ n : El num, (= (int_of_num n) x))))));
