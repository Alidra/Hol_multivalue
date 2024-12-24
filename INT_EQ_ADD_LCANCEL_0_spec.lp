require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301545 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (= (int_add x y) x) (= y (int_of_num (NUMERAL _0))))))));
