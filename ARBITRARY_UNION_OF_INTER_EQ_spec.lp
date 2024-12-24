require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4871095 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (= (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@UNION_OF A) (@ARBITRARY A) P s) ((@UNION_OF A) (@ARBITRARY A) P t)) ((@UNION_OF A) (@ARBITRARY A) P ((@INTER A) s t))))))) (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ (P s) (P t)) ((@UNION_OF A) (@ARBITRARY A) P ((@INTER A) s t))))))))));
