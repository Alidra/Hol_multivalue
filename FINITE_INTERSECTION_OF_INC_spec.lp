require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4876895 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (⇒ (P s) ((@INTERSECTION_OF A) (@FINITE (fun A bool)) P s))))));
