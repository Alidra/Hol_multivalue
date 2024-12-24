require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El (fun nadd bool)) ≔ (dest_hreal (mk_hreal x0));
symbol term4 (x0: El (fun nadd bool)) ≔ ((@= bool) (∃ (λ y0 : El nadd, (= x0 (nadd_eq y0)))));
symbol term2 (x0: El (fun nadd bool)) ≔ (∃ (λ y0 : El nadd, (= x0 (nadd_eq y0))));
symbol term0 (x0: El (fun nadd bool)) ≔ ((λ y0 : El (fun nadd bool), (∃ (λ y1 : El nadd, (= y0 (nadd_eq y1))))) x0);
symbol term3 (x0: El (fun nadd bool)) ≔ ((@= bool) ((λ y0 : El (fun nadd bool), (∃ (λ y1 : El nadd, (= y0 (nadd_eq y1))))) x0));
