require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6160738 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ s : El (fun A bool), (∀ (λ P : El (fun A bool), (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (⇒ ((@FINITE A) s) (= ((@iterate B A) op s (λ x : El A, ((@COND B) (P x) (f x) (g x)))) (op ((@iterate B A) op ((@GSPEC A) (λ GEN_PVAR_248 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_248 (∧ ((@IN A) x s) (P x)) x))))) f) ((@iterate B A) op ((@GSPEC A) (λ GEN_PVAR_249 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_249 (∧ ((@IN A) x s) (¬ (P x))) x))))) g)))))))))))))));
