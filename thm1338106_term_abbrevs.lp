require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El (fun real bool)) ≔ (∀ (λ y0 : El real, (x0 y0)));
symbol term1 (x0: El (fun real bool)) ≔ (∀ (λ y0 : El (prod hreal hreal), (x0 (mk_real (treal_eq y0)))));
symbol term0 (x0: El (fun real bool)) ≔ ((λ y0 : El (fun real bool), (= (∀ (λ y1 : El (prod hreal hreal), (y0 (mk_real (treal_eq y1))))) (∀ (λ y1 : El real, (y0 y1))))) x0);
