require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem322348 [A] (<< : El (fun A (fun A bool))) : Prf (⇒ (∀ (λ H : El (fun (fun A bool) (fun A bool)), (⇒ (∀ (λ f : El (fun A bool), (∀ (λ g : El (fun A bool), (∀ (λ x : El A, (⇒ (∀ (λ z : El A, (⇒ (<< z x) (= (f z) (g z))))) (= (H f x) (H g x))))))))) (∀ (λ f : El (fun A bool), (∀ (λ g : El (fun A bool), (⇒ (∧ (∀ (λ x : El A, (= (f x) (H f x)))) (∀ (λ x : El A, (= (g x) (H g x))))) (= f g))))))))) ((@WF A) <<));
