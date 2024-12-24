require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem364170 [A B] : Prf (∀ (λ R : El (fun A (fun A bool)), (∀ (λ S : El (fun A (fun B (fun B bool))), (⇒ (∧ ((@WF A) R) (∀ (λ a : El A, ((@WF B) (S a))))) ((@WF (prod A B)) ((@GABS (fun (prod A B) (fun (prod A B) bool))) (λ f : El (fun (prod A B) (fun (prod A B) bool)), (∀ (λ r1 : El A, (∀ (λ s1 : El B, ((@GEQ (fun (prod A B) bool)) (f ((@̦‚ A B) r1 s1)) ((@GABS (fun (prod A B) bool)) (λ f' : El (fun (prod A B) bool), (∀ (λ r2 : El A, (∀ (λ s2 : El B, ((@GEQ bool) (f' ((@̦‚ A B) r2 s2)) (∨ (R r1 r2) (∧ (= r1 r2) (S r1 s1 s2)))))))))))))))))))))));
