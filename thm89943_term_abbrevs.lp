require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ ((@ε (fun num (fun num (fun num bool)))) (λ y0 : El type1601, (∀ (λ y1 : El num, (∧ (∀ (λ y2 : El num, (= (y0 y1 y2 (NUMERAL _0)) F))) (∀ (λ y2 : El num, (∀ (λ y3 : El num, (= (y0 y1 y2 (SUC y3)) (∨ (= y2 y3) (y0 y1 y2 y3))))))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0))))))));
