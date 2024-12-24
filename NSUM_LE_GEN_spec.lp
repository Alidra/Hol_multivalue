require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7017399 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ g : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) (<= (f x) (g x))))) ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_299 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_299 (∧ ((@IN A) x s) (¬ (= (g x) (NUMERAL _0)))) x))))))) (<= ((@nsum A) s f) ((@nsum A) s g)))))))));
