require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term4 (x0: El real) ≔ ((λ y0 : El real, (= (sqrt y0) ((@ε real) (λ y1 : El real, (∧ (= (real_sgn y1) (real_sgn y0)) (= (real_pow y1 (NUMERAL (BIT0 (BIT1 _0)))) (real_abs y0))))))) x0);
symbol term0 ≔ (λ y0 : El real, ((@ε real) (λ y1 : El real, (∧ (= (real_sgn y1) (real_sgn y0)) (= (real_pow y1 (NUMERAL (BIT0 (BIT1 _0)))) (real_abs y0))))));
symbol term3 ≔ (∀ (λ y0 : El real, (= (sqrt y0) ((@ε real) (λ y1 : El real, (∧ (= (real_sgn y1) (real_sgn y0)) (= (real_pow y1 (NUMERAL (BIT0 (BIT1 _0)))) (real_abs y0))))))));
symbol term2 (x0: El real) ≔ ((@ε real) (λ y0 : El real, (∧ (= (real_sgn y0) (real_sgn x0)) (= (real_pow y0 (NUMERAL (BIT0 (BIT1 _0)))) (real_abs x0)))));
symbol term1 (x0: El real) ≔ ((λ y0 : El real, ((@ε real) (λ y1 : El real, (∧ (= (real_sgn y1) (real_sgn y0)) (= (real_pow y1 (NUMERAL (BIT0 (BIT1 _0)))) (real_abs y0)))))) x0);
