require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (∀ (λ y0 : El a0, (∀ (λ y1 : El (fun a0 bool), (∀ (λ y2 : El (list a0), (= ((@FILTER a0) y1 ((@CONS a0) y0 y2)) ((@COND (list a0)) (y1 y0) ((@CONS a0) y0 ((@FILTER a0) y1 y2)) ((@FILTER a0) y1 y2)))))))));
