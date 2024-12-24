require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4390595 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (= ((@RESTRICTION A B) s ((@RESTRICTION A B) s f)) ((@RESTRICTION A B) s f))))));
