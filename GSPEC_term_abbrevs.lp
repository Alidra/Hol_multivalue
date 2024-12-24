require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 ≔ (∀ (λ y0 : El (fun a0 bool), (= ((@GSPEC a0) y0) y0)));
symbol term1 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), y0) x0);
symbol term3 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (= ((@GSPEC a0) y0) y0)) x0);
symbol term0 a0 ≔ (λ y0 : El (fun a0 bool), y0);
