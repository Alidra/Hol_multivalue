require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6905935 : Prf (= ((@ε int) (λ x : El int, (∀ (λ y : El int, (∧ (= (int_mul x y) y) (= (int_mul y x) y)))))) (int_of_num (NUMERAL (BIT1 _0))));
