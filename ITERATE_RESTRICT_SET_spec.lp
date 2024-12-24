require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5986609 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ P : El (fun A bool), (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (= ((@iterate B A) op ((@GSPEC A) (λ GEN_PVAR_242 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_242 (∧ ((@IN A) x s) (P x)) x))))) f) ((@iterate B A) op s (λ x : El A, ((@COND B) (P x) (f x) ((@neutral B) op))))))))))))));
