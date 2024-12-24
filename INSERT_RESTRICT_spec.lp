require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3215912 [A] : Prf (∀ (λ P : El (fun A bool), (∀ (λ s : El (fun A bool), (∀ (λ a : El A, (= ((@GSPEC A) (λ GEN_PVAR_8 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_8 (∧ ((@IN A) x ((@INSERT A) a s)) (P x)) x))))) ((@COND (fun A bool)) (P a) ((@INSERT A) a ((@GSPEC A) (λ GEN_PVAR_9 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_9 (∧ ((@IN A) x s) (P x)) x)))))) ((@GSPEC A) (λ GEN_PVAR_10 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_10 (∧ ((@IN A) x s) (P x)) x)))))))))))));
