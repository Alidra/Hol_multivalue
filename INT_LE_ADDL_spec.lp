require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2302294 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_le y (int_add x y)) (int_le (int_of_num (NUMERAL _0)) x))))));
