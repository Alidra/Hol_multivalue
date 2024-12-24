require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (λ y0 : El (type1470 a0 a1), (λ y1 : El (type1470 a0 a1), (λ y2 : El a1, ((@COND (fun a0 bool)) (∃ (λ y3 : El a0, (y0 y2 y3))) (y0 y2) (y1 y2)))));
