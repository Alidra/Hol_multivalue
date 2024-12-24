require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4606457 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A (fun B bool)), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) (∧ ((@FINITE B) (t x)) (<= ((@CARD B) (t x)) n))))) (∧ ((@FINITE A) s) (<= ((@CARD A) s) m))) (∧ ((@FINITE B) ((@UNIONS B) ((@GSPEC (fun B bool)) (λ GEN_PVAR_159 : El (fun B bool), (∃ (λ x : El A, ((@SETSPEC (fun B bool)) GEN_PVAR_159 ((@IN A) x s) (t x)))))))) (<= ((@CARD B) ((@UNIONS B) ((@GSPEC (fun B bool)) (λ GEN_PVAR_160 : El (fun B bool), (∃ (λ x : El A, ((@SETSPEC (fun B bool)) GEN_PVAR_160 ((@IN A) x s) (t x)))))))) (* m n))))))))))));
