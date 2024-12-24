require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3202678 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (= ((@BIJ A B) f s t) (∧ ((@INJ A B) f s t) ((@SURJ A B) f s t)))))))));
