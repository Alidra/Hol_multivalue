require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7028681 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ P : El (fun A bool), (∀ (λ f : El (fun A num), (∀ (λ g : El (fun A num), (⇒ ((@FINITE A) s) (= ((@nsum A) s (λ x : El A, ((@COND num) (P x) (f x) (g x)))) (+ ((@nsum A) ((@GSPEC A) (λ GEN_PVAR_301 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_301 (∧ ((@IN A) x s) (P x)) x))))) f) ((@nsum A) ((@GSPEC A) (λ GEN_PVAR_302 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_302 (∧ ((@IN A) x s) (¬ (P x))) x))))) g))))))))))));
