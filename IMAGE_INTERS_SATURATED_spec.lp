require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3556963 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (⇒ (∧ (¬ (= g (@EMPTY (fun A bool)))) (∀ (λ t : El (fun A bool), (⇒ ((@IN (fun A bool)) t ((@DELETE (fun A bool)) g s)) ((@SUBSET A) ((@GSPEC A) (λ GEN_PVAR_88 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_88 ((@IN B) (f x) ((@IMAGE A B) f t)) x))))) t))))) (= ((@IMAGE A B) f ((@INTERS A) g)) ((@INTERS B) ((@IMAGE (fun A bool) (fun B bool)) ((@IMAGE A B) f) g))))))))));
