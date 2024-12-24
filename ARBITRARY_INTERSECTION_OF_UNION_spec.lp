require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4876619 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (⇒ (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ (P s) (P t)) (P ((@UNION A) s t))))))) (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@INTERSECTION_OF A) (@ARBITRARY A) P s) ((@INTERSECTION_OF A) (@ARBITRARY A) P t)) ((@INTERSECTION_OF A) (@ARBITRARY A) P ((@UNION A) s t))))))))));
