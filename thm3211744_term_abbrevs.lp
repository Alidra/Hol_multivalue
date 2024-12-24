require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 (x0: El (fun a0 bool)) ≔ (∀ (λ y0 : El (fun a0 bool), (= ((@PSUBSET a0) x0 y0) (∧ ((@SUBSET a0) x0 y0) (¬ (= x0 y0))))));
symbol term2 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (= ((@PSUBSET a0) x0 y0) (∧ ((@SUBSET a0) x0 y0) (¬ (= x0 y0))))) x1);
symbol term0 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (∀ (λ y1 : El (fun a0 bool), (= ((@PSUBSET a0) y0 y1) (∧ ((@SUBSET a0) y0 y1) (¬ (= y0 y1))))))) x0);
