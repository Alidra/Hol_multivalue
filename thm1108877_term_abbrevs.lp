require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ ((@ε (fun (prod num (prod num num)) (fun (list a0) (fun (list a1) (list (prod a0 a1)))))) (λ y0 : El (type1303 a0 a1), (∀ (λ y1 : El type1674, (∧ (∀ (λ y2 : El (list a1), (= (y0 y1 (@NIL a0) y2) (@NIL (prod a0 a1))))) (∀ (λ y2 : El a0, (∀ (λ y3 : El (list a0), (∀ (λ y4 : El (list a1), (= (y0 y1 ((@CONS a0) y2 y3) y4) ((@CONS (prod a0 a1)) ((@̦‚ a0 a1) y2 ((@HD a1) y4)) (y0 y1 y3 ((@TL a1) y4)))))))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))));
