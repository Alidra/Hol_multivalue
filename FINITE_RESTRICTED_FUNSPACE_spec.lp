require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4620674 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ k : El (fun A B), (⇒ (∧ ((@FINITE A) s) ((@FINITE B) t)) ((@FINITE (fun A B)) ((@GSPEC (fun A B)) (λ GEN_PVAR_178 : El (fun A B), (∃ (λ f : El (fun A B), ((@SETSPEC (fun A B)) GEN_PVAR_178 (∧ ((@SUBSET B) ((@IMAGE A B) f s) t) ((@SUBSET A) ((@GSPEC A) (λ GEN_PVAR_177 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_177 (¬ (= (f x) (k x))) x))))) s)) f)))))))))))));
