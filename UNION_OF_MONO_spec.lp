require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4844116 [A] : Prf (∀ (λ P : El (fun (fun (fun A bool) bool) bool), (∀ (λ Q : El (fun (fun A bool) bool), (∀ (λ Q' : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@UNION_OF A) P Q s) (∀ (λ x : El (fun A bool), (⇒ (Q x) (Q' x))))) ((@UNION_OF A) P Q' s))))))))));
