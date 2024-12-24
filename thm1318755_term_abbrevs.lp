require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (∀ (λ y0 : El (fun hreal bool), (= (∃ (λ y1 : El nadd, (y0 (mk_hreal (nadd_eq y1))))) (∃ (λ y1 : El hreal, (y0 y1)))))) (∀ (λ y0 : El hreal, (= (mk_hreal (nadd_eq ((@ε nadd) (dest_hreal y0)))) y0))));
symbol term2 (x0: El (fun hreal bool)) ≔ ((λ y0 : El (fun hreal bool), (= (∃ (λ y1 : El nadd, (y0 (mk_hreal (nadd_eq y1))))) (∃ (λ y1 : El hreal, (y0 y1))))) x0);
symbol term1 ≔ (∀ (λ y0 : El (fun hreal bool), (= (∃ (λ y1 : El nadd, (y0 (mk_hreal (nadd_eq y1))))) (∃ (λ y1 : El hreal, (y0 y1))))));
