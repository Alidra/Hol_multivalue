require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4889827 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (= (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@UNION_OF A) (@FINITE (fun A bool)) P s) ((@UNION_OF A) (@FINITE (fun A bool)) P t)) ((@UNION_OF A) (@FINITE (fun A bool)) P ((@INTER A) s t))))))) (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ (P s) (P t)) ((@UNION_OF A) (@FINITE (fun A bool)) P ((@INTER A) s t))))))))));
