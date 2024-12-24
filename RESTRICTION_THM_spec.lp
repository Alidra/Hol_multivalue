require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4386714 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (= ((@RESTRICTION A B) s f) (λ x : El A, ((@COND B) ((@IN A) x s) (f x) (@ARB B))))))));
