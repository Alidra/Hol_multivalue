require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem346581 [A] (<< : El (fun A (fun A bool))) : Prf (⇒ (∀ (λ H : El (fun (fun A num) (fun A num)), (⇒ (∀ (λ f : El (fun A num), (∀ (λ g : El (fun A num), (∀ (λ x : El A, (⇒ (∀ (λ z : El A, (⇒ (<< z x) (= (f z) (g z))))) (= (H f x) (H g x))))))))) (∃ (λ f : El (fun A num), (∀ (λ x : El A, (= (f x) (H f x))))))))) ((@WF A) <<));
