require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) ≔ ((λ y0 : El num, (∀ (λ y1 : El num, (∀ (λ y2 : El num, (= ((@IN num) y2 (… y0 y1)) (∧ (<= y0 y2) (<= y2 y1)))))))) x0);
symbol term2 (x0: El num) (x1: El num) ≔ ((λ y0 : El num, (∀ (λ y1 : El num, (= ((@IN num) y1 (… x0 y0)) (∧ (<= x0 y1) (<= y1 y0)))))) x1);
symbol term1 (x0: El num) ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= ((@IN num) y1 (… x0 y0)) (∧ (<= x0 y1) (<= y1 y0)))))));
symbol term3 (x0: El num) (x1: El num) ≔ (∀ (λ y0 : El num, (= ((@IN num) y0 (… x0 x1)) (∧ (<= x0 y0) (<= y0 x1)))));
symbol term4 (x0: El num) (x1: El num) (x2: El num) ≔ ((λ y0 : El num, (= ((@IN num) y0 (… x0 x1)) (∧ (<= x0 y0) (<= y0 x1)))) x2);
