require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7168710 [A B] : Prf (∀ (λ R : El (fun A (fun B bool)), (∀ (λ g : El (fun A real), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@∃! B) (λ y : El B, (∧ ((@IN B) y t) (R x y)))))))) (= ((@sum B) t (λ y : El B, ((@sum A) ((@GSPEC A) (λ GEN_PVAR_326 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_326 (∧ ((@IN A) x s) (R x y)) x))))) g))) ((@sum A) s g)))))))))));
