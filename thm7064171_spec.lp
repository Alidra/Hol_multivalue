require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7064171 : Prf (= (= ((@ε real) (λ x : El real, (∀ (λ y : El real, (∧ (= (real_add x y) y) (= (real_add y x) y)))))) (real_of_num (NUMERAL _0))) (= ((@neutral real) real_add) (real_of_num (NUMERAL _0))));
