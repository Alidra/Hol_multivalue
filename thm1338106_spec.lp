require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1338106 (P : El (fun real bool)) : Prf (= ((λ P' : El (fun real bool), (= (∀ (λ x : El (prod hreal hreal), (P' (mk_real (treal_eq x))))) (∀ (λ x : El real, (P' x))))) P) (= (∀ (λ x : El (prod hreal hreal), (P (mk_real (treal_eq x))))) (∀ (λ x : El real, (P x)))));
