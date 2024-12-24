require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1509970 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (real_le x (real_add x y)) (real_le (real_of_num (NUMERAL _0)) y))))));
