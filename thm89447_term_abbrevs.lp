require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ ((@ε (fun (prod num num) (fun num (fun num bool)))) (λ y0 : El type1323, (∀ (λ y1 : El (prod num num), (∧ (∀ (λ y2 : El num, (= (y0 y1 y2 (NUMERAL _0)) (= y2 (NUMERAL _0))))) (∀ (λ y2 : El num, (∀ (λ y3 : El num, (= (y0 y1 y2 (SUC y3)) (∨ (= y2 (SUC y3)) (y0 y1 y2 y3))))))))))) ((@̦‚ num num) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0)))))))));
