require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6992800 [A B] : Prf (∀ (λ R : El (fun A (fun B bool)), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ k : El (fun B num), (⇒ (∧ ((@FINITE A) s) (∧ ((@FINITE B) t) (∀ (λ j : El B, (⇒ ((@IN B) j t) (= ((@CARD A) ((@GSPEC A) (λ GEN_PVAR_291 : El A, (∃ (λ i : El A, ((@SETSPEC A) GEN_PVAR_291 (∧ ((@IN A) i s) (R i j)) i)))))) (k j))))))) (= ((@nsum A) s (λ i : El A, ((@CARD B) ((@GSPEC B) (λ GEN_PVAR_292 : El B, (∃ (λ j : El B, ((@SETSPEC B) GEN_PVAR_292 (∧ ((@IN B) j t) (R i j)) j)))))))) ((@nsum B) t (λ i : El B, (k i)))))))))))));
