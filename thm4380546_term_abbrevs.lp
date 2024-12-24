require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 ≔ (∀ (λ y0 : El (fun a0 bool), (∀ (λ y1 : El (type686 a1), (= ((@CROSS a1 a0) y0 ((@INTERS a1) y1)) ((@COND (fun (prod a0 a1) bool)) (= y1 (@EMPTY (fun a1 bool))) ((@CROSS a1 a0) y0 (@UNIV a1)) ((@INTERS (prod a0 a1)) ((@GSPEC (fun (prod a0 a1) bool)) (λ y2 : El (type1210 a0 a1), (∃ (λ y3 : El (fun a1 bool), ((@SETSPEC (fun (prod a0 a1) bool)) y2 ((@IN (fun a1 bool)) y3 y1) ((@CROSS a1 a0) y0 y3)))))))))))));
symbol term0 a0 a1 (x0: El (fun a0 bool)) ≔ (∀ (λ y0 : El (type686 a1), (= ((@CROSS a1 a0) x0 ((@INTERS a1) y0)) ((@COND (fun (prod a0 a1) bool)) (= y0 (@EMPTY (fun a1 bool))) ((@CROSS a1 a0) x0 (@UNIV a1)) ((@INTERS (prod a0 a1)) ((@GSPEC (fun (prod a0 a1) bool)) (λ y1 : El (type1210 a0 a1), (∃ (λ y2 : El (fun a1 bool), ((@SETSPEC (fun (prod a0 a1) bool)) y1 ((@IN (fun a1 bool)) y2 y0) ((@CROSS a1 a0) x0 y2)))))))))));
