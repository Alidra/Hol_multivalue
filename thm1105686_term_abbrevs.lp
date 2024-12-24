require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ ((@ε (fun (prod num num) (fun num (fun (list a0) a0)))) (λ y0 : El (type1322 a0), (∀ (λ y1 : El (prod num num), (∧ (∀ (λ y2 : El (list a0), (= (y0 y1 (NUMERAL _0) y2) ((@HD a0) y2)))) (∀ (λ y2 : El num, (∀ (λ y3 : El (list a0), (= (y0 y1 (SUC y2) y3) (y0 y1 y2 ((@TL a0) y3))))))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0))))))))));
