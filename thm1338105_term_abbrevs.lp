require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 ≔ (∀ (λ y0 : El (fun real bool), (= (∀ (λ y1 : El (prod hreal hreal), (y0 (mk_real (treal_eq y1))))) (∀ (λ y1 : El real, (y0 y1))))));
symbol term0 ≔ (∧ (∀ (λ y0 : El (fun real bool), (= (∀ (λ y1 : El (prod hreal hreal), (y0 (mk_real (treal_eq y1))))) (∀ (λ y1 : El real, (y0 y1)))))) (∧ (∀ (λ y0 : El (fun real bool), (= (∃ (λ y1 : El (prod hreal hreal), (y0 (mk_real (treal_eq y1))))) (∃ (λ y1 : El real, (y0 y1)))))) (∀ (λ y0 : El real, (= (mk_real (treal_eq ((@ε (prod hreal hreal)) (dest_real y0)))) y0)))));
symbol term2 (x0: El (fun real bool)) ≔ ((λ y0 : El (fun real bool), (= (∀ (λ y1 : El (prod hreal hreal), (y0 (mk_real (treal_eq y1))))) (∀ (λ y1 : El real, (y0 y1))))) x0);
