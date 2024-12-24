require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1142383 [_26886 _26887] : Prf (∀ (λ P : El (fun _26887 (fun _26886 bool)), (∀ (λ l : El (list _26886), (= (∃ (λ x : El _26887, ((@EX _26886) (P x) l))) ((@EX _26886) (λ s : El _26886, (∃ (λ x : El _26887, (P x s)))) l))))));
