require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 a3 ≔ (∧ (∀ (λ y0 : El (fun a0 bool), (∀ (λ y1 : El (type686 a1), (= ((@CROSS a1 a0) y0 ((@UNIONS a1) y1)) ((@UNIONS (prod a0 a1)) ((@GSPEC (fun (prod a0 a1) bool)) (λ y2 : El (type1210 a0 a1), (∃ (λ y3 : El (fun a1 bool), ((@SETSPEC (fun (prod a0 a1) bool)) y2 ((@IN (fun a1 bool)) y3 y1) ((@CROSS a1 a0) y0 y3)))))))))))) (∀ (λ y0 : El (type686 a2), (∀ (λ y1 : El (fun a3 bool), (= ((@CROSS a3 a2) ((@UNIONS a2) y0) y1) ((@UNIONS (prod a2 a3)) ((@GSPEC (fun (prod a2 a3) bool)) (λ y2 : El (type1210 a2 a3), (∃ (λ y3 : El (fun a2 bool), ((@SETSPEC (fun (prod a2 a3) bool)) y2 ((@IN (fun a2 bool)) y3 y0) ((@CROSS a3 a2) y3 y1)))))))))))));
