require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4845623 [A] : Prf (∀ (λ P : El (fun (fun (fun A bool) bool) bool), (∀ (λ Q : El (fun (fun A bool) bool), (∀ (λ Q' : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@INTERSECTION_OF A) P Q s) (∀ (λ x : El (fun A bool), (⇒ (Q x) (Q' x))))) ((@INTERSECTION_OF A) P Q' s))))))))));
