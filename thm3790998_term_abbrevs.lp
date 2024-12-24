require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (∀ (λ y0 : El a1, (∀ (λ y1 : El (fun a0 bool), (∀ (λ y2 : El num, (∀ (λ y3 : El a1, (∀ (λ y4 : El (type1411 a0 a1), (= ((@FINREC a0 a1) y4 y0 y1 y3 (SUC y2)) (∃ (λ y5 : El a0, (∃ (λ y6 : El a1, (∧ ((@IN a0) y5 y1) (∧ ((@FINREC a0 a1) y4 y0 ((@DELETE a0) y1 y5) y6 y2) (= y3 (y4 y5 y6)))))))))))))))))));
