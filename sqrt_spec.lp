require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1868831 : Prf (∀ (λ x : El real, (= (sqrt x) ((@ε real) (λ y : El real, (∧ (= (real_sgn y) (real_sgn x)) (= (real_pow y (NUMERAL (BIT0 (BIT1 _0)))) (real_abs x))))))));
