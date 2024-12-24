require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem57687 [A B] : Prf (∀ (λ P : El (fun A (fun B bool)), (∀ (λ Q : El (fun (prod A B) bool), (⇒ (∧ (∃ (λ x : El A, (∃ (λ y : El B, (P x y))))) (∀ (λ x : El A, (∀ (λ y : El B, (⇒ (P x y) (Q ((@̦‚ A B) x y)))))))) (Q ((@ε (prod A B)) ((@GABS (fun (prod A B) bool)) (λ f : El (fun (prod A B) bool), (∀ (λ x : El A, (∀ (λ y : El B, ((@GEQ bool) (f ((@̦‚ A B) x y)) (P x y)))))))))))))));
