require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ ((@ε (fun (prod num (prod num num)) (fun int (fun int int)))) (λ y0 : El type1305, (∀ (λ y1 : El type1674, (∀ (λ y2 : El int, (∀ (λ y3 : El int, ((@COND bool) (= y3 (int_of_num (NUMERAL _0))) (∧ (= (div y2 y3) (int_of_num (NUMERAL _0))) (= (y0 y1 y2 y3) y2)) (∧ (int_le (int_of_num (NUMERAL _0)) (y0 y1 y2 y3)) (∧ (int_lt (y0 y1 y2 y3) (int_abs y3)) (= y2 (int_add (int_mul (div y2 y3) y3) (y0 y1 y2 y3))))))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))))));
