require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ ((@ε (fun (prod num (prod num num)) (fun (fun a0 a1) (fun (list a0) (list a1))))) (λ y0 : El (type1297 a0 a1), (∀ (λ y1 : El type1674, (∧ (∀ (λ y2 : El (fun a0 a1), (= (y0 y1 y2 (@NIL a0)) (@NIL a1)))) (∀ (λ y2 : El (fun a0 a1), (∀ (λ y3 : El a0, (∀ (λ y4 : El (list a0), (= (y0 y1 y2 ((@CONS a0) y3 y4)) ((@CONS a1) (y2 y3) (y0 y1 y2 y4))))))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))));
