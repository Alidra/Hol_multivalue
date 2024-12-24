require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem359527 [A] : Prf (∀ (λ << : El (fun A (fun A bool)), (∀ (λ <<< : El (fun A (fun A bool)), (⇒ (∧ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (<< x y) (<<< x y)))))) ((@WF A) <<<)) ((@WF A) <<))))));
