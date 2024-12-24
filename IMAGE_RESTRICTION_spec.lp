require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4392828 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ ((@SUBSET A) s t) (= ((@IMAGE A B) ((@RESTRICTION A B) t f) s) ((@IMAGE A B) f s)))))))));
