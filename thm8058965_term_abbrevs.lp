require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 a1 a2 a3 (x0: El (type1644 a0 a1 a2 a3)) (x1: El (type1633 a0 a1 a2 a3)) (x2: El a3) (x3: El a2) ≔ ((@COND a0) (∃ (λ y0 : El a1, (= ((@FST (fun a1 a2) (fun a3 (fun a1 a0))) x0 y0) x3))) ((@SND (fun a1 a2) (fun a3 (fun a1 a0))) x0 x2 ((@ε a1) (λ y0 : El a1, (= ((@FST (fun a1 a2) (fun a3 (fun a1 a0))) x0 y0) x3)))) ((@CASEWISE a0 a1 a2 a3) x1 x2 x3));
symbol term1 a0 a1 a2 a3 (x0: El (type1644 a0 a1 a2 a3)) (x1: El (type1633 a0 a1 a2 a3)) (x2: El a3) (x3: El a2) ≔ ((@CASEWISE a0 a1 a2 a3) ((@CONS (prod (fun a1 a2) (fun a3 (fun a1 a0)))) x0 x1) x2 x3);
symbol term0 a0 a1 a2 a3 (x0: El (type1644 a0 a1 a2 a3)) (x1: El (type1633 a0 a1 a2 a3)) (x2: El a3) (x3: El a2) ≔ ((λ y0 : El a2, (= ((@CASEWISE a0 a1 a2 a3) ((@CONS (prod (fun a1 a2) (fun a3 (fun a1 a0)))) x0 x1) x2 y0) ((@COND a0) (∃ (λ y1 : El a1, (= ((@FST (fun a1 a2) (fun a3 (fun a1 a0))) x0 y1) y0))) ((@SND (fun a1 a2) (fun a3 (fun a1 a0))) x0 x2 ((@ε a1) (λ y1 : El a1, (= ((@FST (fun a1 a2) (fun a3 (fun a1 a0))) x0 y1) y0)))) ((@CASEWISE a0 a1 a2 a3) x1 x2 y0)))) x3);
