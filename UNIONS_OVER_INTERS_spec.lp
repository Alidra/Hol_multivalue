require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3486241 [A B] : Prf (∀ (λ f : El (fun A (fun (fun B bool) bool)), (∀ (λ s : El (fun A bool), (= ((@UNIONS B) ((@GSPEC (fun B bool)) (λ GEN_PVAR_77 : El (fun B bool), (∃ (λ x : El A, ((@SETSPEC (fun B bool)) GEN_PVAR_77 ((@IN A) x s) ((@INTERS B) (f x)))))))) ((@INTERS B) ((@GSPEC (fun B bool)) (λ GEN_PVAR_81 : El (fun B bool), (∃ (λ g : El (fun A (fun B bool)), ((@SETSPEC (fun B bool)) GEN_PVAR_81 (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@IN (fun B bool)) (g x) (f x))))) ((@UNIONS B) ((@GSPEC (fun B bool)) (λ GEN_PVAR_80 : El (fun B bool), (∃ (λ x : El A, ((@SETSPEC (fun B bool)) GEN_PVAR_80 ((@IN A) x s) (g x))))))))))))))))));
