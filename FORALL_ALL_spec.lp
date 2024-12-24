require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1145518 [_26916 _26917] : Prf (∀ (λ P : El (fun _26917 (fun _26916 bool)), (∀ (λ l : El (list _26916), (= (∀ (λ x : El _26917, ((@ALL _26916) (P x) l))) ((@ALL _26916) (λ s : El _26916, (∀ (λ x : El _26917, (P x s)))) l))))));
