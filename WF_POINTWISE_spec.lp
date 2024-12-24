require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem365114 [A B] (<< : El (fun A (fun A bool))) (<<< : El (fun B (fun B bool))) : Prf (⇒ (∧ ((@WF A) <<) ((@WF B) <<<)) ((@WF (prod A B)) ((@GABS (fun (prod A B) (fun (prod A B) bool))) (λ f : El (fun (prod A B) (fun (prod A B) bool)), (∀ (λ x1 : El A, (∀ (λ y1 : El B, ((@GEQ (fun (prod A B) bool)) (f ((@̦‚ A B) x1 y1)) ((@GABS (fun (prod A B) bool)) (λ f' : El (fun (prod A B) bool), (∀ (λ x2 : El A, (∀ (λ y2 : El B, ((@GEQ bool) (f' ((@̦‚ A B) x2 y2)) (∧ (<< x1 x2) (<<< y1 y2))))))))))))))))));
