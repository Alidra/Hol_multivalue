require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1740648 : Prf (∀ (λ x : El real, (∨ (= (real_sgn x) (real_of_num (NUMERAL _0))) (∨ (= (real_sgn x) (real_of_num (NUMERAL (BIT1 _0)))) (= (real_sgn x) (real_neg (real_of_num (NUMERAL (BIT1 _0)))))))));
