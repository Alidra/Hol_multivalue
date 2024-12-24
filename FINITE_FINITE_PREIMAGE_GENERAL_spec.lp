require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3617662 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE B) t) (∀ (λ y : El B, (⇒ ((@IN B) y t) ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_98 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_98 (∧ ((@IN A) x s) (= (f x) y)) x)))))))))) ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_99 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_99 (∧ ((@IN A) x s) ((@IN B) (f x) t)) x)))))))))))));
