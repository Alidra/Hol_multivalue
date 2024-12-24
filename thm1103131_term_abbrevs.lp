require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ ((@ε (fun (prod num (prod num num)) (fun a0 (fun (list a0) bool)))) (λ y0 : El (type1304 a0), (∀ (λ y1 : El type1674, (∧ (∀ (λ y2 : El a0, (= (y0 y1 y2 (@NIL a0)) F))) (∀ (λ y2 : El a0, (∀ (λ y3 : El a0, (∀ (λ y4 : El (list a0), (= (y0 y1 y3 ((@CONS a0) y2 y4)) (∨ (= y3 y2) (y0 y1 y3 y4))))))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))));
