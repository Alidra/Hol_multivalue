require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 a3 ≔ (∀ (λ y0 : El (type1644 a0 a1 a2 a3), (∀ (λ y1 : El (type1633 a0 a1 a2 a3), (∀ (λ y2 : El a3, (∀ (λ y3 : El a2, (= ((@CASEWISE a0 a1 a2 a3) ((@CONS (prod (fun a1 a2) (fun a3 (fun a1 a0)))) y0 y1) y2 y3) ((@COND a0) (∃ (λ y4 : El a1, (= ((@FST (fun a1 a2) (fun a3 (fun a1 a0))) y0 y4) y3))) ((@SND (fun a1 a2) (fun a3 (fun a1 a0))) y0 y2 ((@ε a1) (λ y4 : El a1, (= ((@FST (fun a1 a2) (fun a3 (fun a1 a0))) y0 y4) y3)))) ((@CASEWISE a0 a1 a2 a3) y1 y2 y3)))))))))));
