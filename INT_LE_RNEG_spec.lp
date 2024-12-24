require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2303280 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_le x (int_neg y)) (int_le (int_add x y) (int_of_num (NUMERAL _0))))))));
