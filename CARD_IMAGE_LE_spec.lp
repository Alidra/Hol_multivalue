require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4008003 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (<= ((@CARD B) ((@IMAGE A B) f s)) ((@CARD A) s)))))));
