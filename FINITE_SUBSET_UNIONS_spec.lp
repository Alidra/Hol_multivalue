require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3756509 [A] : Prf (∀ (λ f : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) ((@SUBSET A) s ((@UNIONS A) f))) (∃ (λ f' : El (fun (fun A bool) bool), (∧ ((@FINITE (fun A bool)) f') (∧ ((@SUBSET (fun A bool)) f' f) ((@SUBSET A) s ((@UNIONS A) f')))))))))));
