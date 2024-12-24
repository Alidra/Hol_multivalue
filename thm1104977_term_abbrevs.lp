require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 ≔ ((@ε (fun (prod num (prod num (prod num num))) (fun (fun a1 (fun a2 a0)) (fun (list a1) (fun (list a2) (list a0)))))) (λ y0 : El (type1286 a0 a1 a2), (∀ (λ y1 : El type1673, (∧ (∀ (λ y2 : El (type1475 a0 a1 a2), (∀ (λ y3 : El (list a2), (= (y0 y1 y2 (@NIL a1) y3) (@NIL a0)))))) (∀ (λ y2 : El a1, (∀ (λ y3 : El (type1475 a0 a1 a2), (∀ (λ y4 : El (list a1), (∀ (λ y5 : El (list a2), (= (y0 y1 y3 ((@CONS a1) y2 y4) y5) ((@CONS a0) (y3 y2 ((@HD a2) y5)) (y0 y1 y3 y4 ((@TL a2) y5)))))))))))))))) ((@̦‚ num (prod num (prod num num))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))))));
