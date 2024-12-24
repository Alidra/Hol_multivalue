require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2309350 : Prf (∀ (λ x : El int, (∨ (= (int_sgn x) (int_of_num (NUMERAL _0))) (∨ (= (int_sgn x) (int_of_num (NUMERAL (BIT1 _0)))) (= (int_sgn x) (int_neg (int_of_num (NUMERAL (BIT1 _0)))))))));
