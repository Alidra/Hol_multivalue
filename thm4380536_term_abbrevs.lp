require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El (type686 a0)) ≔ (∀ (λ y0 : El (fun a1 bool), (= ((@CROSS a1 a0) ((@INTERS a0) x0) y0) ((@COND (fun (prod a0 a1) bool)) (= x0 (@EMPTY (fun a0 bool))) ((@CROSS a1 a0) (@UNIV a0) y0) ((@INTERS (prod a0 a1)) ((@GSPEC (fun (prod a0 a1) bool)) (λ y1 : El (type1210 a0 a1), (∃ (λ y2 : El (fun a0 bool), ((@SETSPEC (fun (prod a0 a1) bool)) y1 ((@IN (fun a0 bool)) y2 x0) ((@CROSS a1 a0) y2 y0)))))))))));
symbol term1 a0 a1 ≔ (∀ (λ y0 : El (type686 a0), (∀ (λ y1 : El (fun a1 bool), (= ((@CROSS a1 a0) ((@INTERS a0) y0) y1) ((@COND (fun (prod a0 a1) bool)) (= y0 (@EMPTY (fun a0 bool))) ((@CROSS a1 a0) (@UNIV a0) y1) ((@INTERS (prod a0 a1)) ((@GSPEC (fun (prod a0 a1) bool)) (λ y2 : El (type1210 a0 a1), (∃ (λ y3 : El (fun a0 bool), ((@SETSPEC (fun (prod a0 a1) bool)) y2 ((@IN (fun a0 bool)) y3 y0) ((@CROSS a1 a0) y3 y1)))))))))))));
