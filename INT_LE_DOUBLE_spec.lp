require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2302379 : Prf (∀ (λ x : El int, (= (int_le (int_of_num (NUMERAL _0)) (int_add x x)) (int_le (int_of_num (NUMERAL _0)) x))));
