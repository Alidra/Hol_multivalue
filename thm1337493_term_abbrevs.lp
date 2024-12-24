require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El type1233) ≔ (∃ (λ y0 : El (prod hreal hreal), (= x0 (treal_eq y0))));
symbol term4 (x0: El type1233) ≔ ((@= bool) (∃ (λ y0 : El (prod hreal hreal), (= x0 (treal_eq y0)))));
symbol term1 (x0: El type1233) ≔ (dest_real (mk_real x0));
symbol term0 (x0: El type1233) ≔ ((λ y0 : El type1233, (∃ (λ y1 : El (prod hreal hreal), (= y0 (treal_eq y1))))) x0);
symbol term3 (x0: El type1233) ≔ ((@= bool) ((λ y0 : El type1233, (∃ (λ y1 : El (prod hreal hreal), (= y0 (treal_eq y1))))) x0));
