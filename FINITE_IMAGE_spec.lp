require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3615104 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) ((@FINITE B) ((@IMAGE A B) f s)))))));
