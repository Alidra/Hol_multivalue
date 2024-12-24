require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4390547 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ f : El (fun A B), (⇒ ((@SUBSET A) s t) (= ((@RESTRICTION A B) s ((@RESTRICTION A B) t f)) ((@RESTRICTION A B) s f)))))))));
