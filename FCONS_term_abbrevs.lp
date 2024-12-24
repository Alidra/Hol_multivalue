require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (∀ (λ y0 : El a0, (∀ (λ y1 : El (fun num a0), (∀ (λ y2 : El num, (= ((@FCONS a0) y0 y1 (SUC y2)) (y1 y2))))))));
symbol term1 a0 ≔ (∀ (λ y0 : El a0, (∀ (λ y1 : El (fun num a0), (= ((@FCONS a0) y0 y1 (NUMERAL _0)) y0)))));
symbol term2 a0 ≔ (∧ (∀ (λ y0 : El a0, (∀ (λ y1 : El (fun num a0), (= ((@FCONS a0) y0 y1 (NUMERAL _0)) y0))))) (∀ (λ y0 : El a0, (∀ (λ y1 : El (fun num a0), (∀ (λ y2 : El num, (= ((@FCONS a0) y0 y1 (SUC y2)) (y1 y2)))))))));
