require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4842609 [A] : Prf (∀ (λ P : El (fun (fun (fun A bool) bool) bool), (∀ (λ Q : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (⇒ (∧ (P ((@INSERT (fun A bool)) s (@EMPTY (fun A bool)))) (Q s)) ((@INTERSECTION_OF A) P Q s))))))));
