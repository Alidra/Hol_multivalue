require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3197567 [A] : Prf (∀ (λ FINITE' : El (fun (fun A bool) bool), (⇒ (∧ (FINITE' (@EMPTY A)) (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ (FINITE' s) (FINITE' ((@INSERT A) x s)))))))) (∀ (λ a : El (fun A bool), (⇒ ((@FINITE A) a) (FINITE' a)))))));
