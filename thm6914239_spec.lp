require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6914239 : Prf (= (= ((@ε int) (λ x : El int, (∀ (λ y : El int, (∧ (= (int_add x y) y) (= (int_add y x) y)))))) (int_of_num (NUMERAL _0))) (= ((@neutral int) int_add) (int_of_num (NUMERAL _0))));
