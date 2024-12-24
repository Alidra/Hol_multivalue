require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (λ y0 : El (fun a0 bool), ((@>=_c a0 num) (@UNIV num) y0));
symbol term1 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), ((@>=_c a0 num) (@UNIV num) y0)) x0);
symbol term3 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (= ((@COUNTABLE a0) y0) ((@>=_c a0 num) (@UNIV num) y0))) x0);
symbol term2 a0 ≔ (∀ (λ y0 : El (fun a0 bool), (= ((@COUNTABLE a0) y0) ((@>=_c a0 num) (@UNIV num) y0))));
