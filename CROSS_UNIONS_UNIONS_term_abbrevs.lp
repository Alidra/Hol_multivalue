require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (∀ (λ y0 : El (type686 a0), (∀ (λ y1 : El (type686 a1), (= ((@CROSS a1 a0) ((@UNIONS a0) y0) ((@UNIONS a1) y1)) ((@UNIONS (prod a0 a1)) ((@GSPEC (fun (prod a0 a1) bool)) (λ y2 : El (type1210 a0 a1), (∃ (λ y3 : El (fun a0 bool), (∃ (λ y4 : El (fun a1 bool), ((@SETSPEC (fun (prod a0 a1) bool)) y2 (∧ ((@IN (fun a0 bool)) y3 y0) ((@IN (fun a1 bool)) y4 y1)) ((@CROSS a1 a0) y3 y4))))))))))))));
