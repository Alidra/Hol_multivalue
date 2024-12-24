require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4382798 [A B] : Prf (∀ (λ s : El (fun A bool), (= ((@EXTENSIONAL A B) s) ((@GSPEC (fun A B)) (λ GEN_PVAR_139 : El (fun A B), (∃ (λ f : El (fun A B), ((@SETSPEC (fun A B)) GEN_PVAR_139 (∀ (λ x : El A, (⇒ (¬ ((@IN A) x s)) (= (f x) (@ARB B))))) f))))))));
