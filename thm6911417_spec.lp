require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6911417 : Prf (= ((@ε real) (λ x : El real, (∀ (λ y : El real, (∧ (= (real_mul x y) y) (= (real_mul y x) y)))))) (real_of_num (NUMERAL (BIT1 _0))));
