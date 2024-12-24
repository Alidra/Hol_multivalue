require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3698379 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (= (∧ ((@FINITE B) t) ((@SUBSET B) t ((@IMAGE A B) f s))) (∃ (λ s' : El (fun A bool), (∧ ((@FINITE A) s') (∧ ((@SUBSET A) s' s) (= t ((@IMAGE A B) f s')))))))))))));
