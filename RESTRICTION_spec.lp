require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4386626 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (∀ (λ x : El A, (= ((@RESTRICTION A B) s f x) ((@COND B) ((@IN A) x s) (f x) (@ARB B)))))))));
