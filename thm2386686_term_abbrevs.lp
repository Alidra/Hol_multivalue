require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ ((@ε (fun (prod num (prod num num)) (fun int (fun int int)))) (λ y0 : El type1305, (∀ (λ y1 : El type1674, (∃ (λ y2 : El type1551, (∀ (λ y3 : El int, (∀ (λ y4 : El int, ((@COND bool) (= y4 (int_of_num (NUMERAL _0))) (∧ (= (y0 y1 y3 y4) (int_of_num (NUMERAL _0))) (= (y2 y3 y4) y3)) (∧ (int_le (int_of_num (NUMERAL _0)) (y2 y3 y4)) (∧ (int_lt (y2 y3 y4) (int_abs y4)) (= y3 (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4))))))))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))))));
