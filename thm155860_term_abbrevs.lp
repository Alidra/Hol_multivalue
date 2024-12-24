require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ ((@ε (fun (prod num (prod num num)) (fun num (fun num num)))) (λ y0 : El type1306, (∀ (λ y1 : El type1674, (∀ (λ y2 : El num, (∀ (λ y3 : El num, ((@COND bool) (= y3 (NUMERAL _0)) (∧ (= (DIV y2 y3) (NUMERAL _0)) (= (y0 y1 y2 y3) y2)) (∧ (= y2 (+ (* (DIV y2 y3) y3) (y0 y1 y2 y3))) (< (y0 y1 y2 y3) y3)))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))));
