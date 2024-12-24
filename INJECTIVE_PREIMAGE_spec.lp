require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5056129 [A B] : Prf (∀ (λ f : El (fun A B), (= (∀ (λ t : El (fun B bool), (∀ (λ t' : El (fun B bool), (⇒ (= ((@GSPEC A) (λ GEN_PVAR_223 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_223 ((@IN B) (f x) t) x))))) ((@GSPEC A) (λ GEN_PVAR_224 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_224 ((@IN B) (f x) t') x)))))) (= t t')))))) (= ((@IMAGE A B) f (@UNIV A)) (@UNIV B)))));
