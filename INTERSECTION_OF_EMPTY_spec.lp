require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4851880 [A] : Prf (∀ (λ P : El (fun (fun (fun A bool) bool) bool), (∀ (λ Q : El (fun (fun A bool) bool), (⇒ (P (@EMPTY (fun A bool))) ((@INTERSECTION_OF A) P Q (@UNIV A)))))));
