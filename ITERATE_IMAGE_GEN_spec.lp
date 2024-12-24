require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6158399 [A B C] : Prf (∀ (λ op : El (fun C (fun C C)), (⇒ ((@monoidal C) op) (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A C), (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (= ((@iterate C A) op s g) ((@iterate C B) op ((@IMAGE A B) f s) (λ y : El B, ((@iterate C A) op ((@GSPEC A) (λ GEN_PVAR_245 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_245 (∧ ((@IN A) x s) (= (f x) y)) x))))) g))))))))))))));
