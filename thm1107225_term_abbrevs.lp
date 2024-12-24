require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ ((@ε (fun (prod num (prod num (prod num (prod num num)))) (fun a1 (fun (list (prod a1 a0)) a0)))) (λ y0 : El (type1276 a0 a1), (∀ (λ y1 : El type1672, (∀ (λ y2 : El (prod a1 a0), (∀ (λ y3 : El a1, (∀ (λ y4 : El (type1641 a0 a1), (= (y0 y1 y3 ((@CONS (prod a1 a0)) y2 y4)) ((@COND a0) (= ((@FST a1 a0) y2) y3) ((@SND a1 a0) y2) (y0 y1 y3 y4)))))))))))) ((@̦‚ num (prod num (prod num (prod num num)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num (prod num (prod num num))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))))));
