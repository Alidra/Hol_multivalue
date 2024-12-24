require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 a0 ≔ (∀ (λ y0 : El (fun a0 bool), (= ((@list_of_set a0) y0) ((@ε (list a0)) (λ y1 : El (list a0), (∧ (= ((@set_of_list a0) y1) y0) (= ((@LENGTH a0) y1) ((@CARD a0) y0))))))));
symbol term0 a0 ≔ (λ y0 : El (fun a0 bool), ((@ε (list a0)) (λ y1 : El (list a0), (∧ (= ((@set_of_list a0) y1) y0) (= ((@LENGTH a0) y1) ((@CARD a0) y0))))));
symbol term4 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (= ((@list_of_set a0) y0) ((@ε (list a0)) (λ y1 : El (list a0), (∧ (= ((@set_of_list a0) y1) y0) (= ((@LENGTH a0) y1) ((@CARD a0) y0))))))) x0);
symbol term1 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), ((@ε (list a0)) (λ y1 : El (list a0), (∧ (= ((@set_of_list a0) y1) y0) (= ((@LENGTH a0) y1) ((@CARD a0) y0)))))) x0);
symbol term2 a0 (x0: El (fun a0 bool)) ≔ ((@ε (list a0)) (λ y0 : El (list a0), (∧ (= ((@set_of_list a0) y0) x0) (= ((@LENGTH a0) y0) ((@CARD a0) x0)))));
