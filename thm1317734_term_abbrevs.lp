require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El nadd) ≔ (λ y0 : El nadd, (= (nadd_eq x0) (nadd_eq y0)));
symbol term1 (x0: El nadd) ≔ (∃ (λ y0 : El nadd, (= (nadd_eq x0) (nadd_eq y0))));
symbol term0 (x0: El nadd) ≔ ((λ y0 : El (fun nadd bool), (∃ (λ y1 : El nadd, (= y0 (nadd_eq y1))))) (nadd_eq x0));
