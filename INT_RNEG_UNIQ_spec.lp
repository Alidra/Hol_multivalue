require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308978 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (= (int_add x y) (int_of_num (NUMERAL _0))) (= y (int_neg x)))))));
