require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem339314 [A B] (<< : El (fun A (fun A bool))) (h1 : Prf ((@WF A) <<)) : Prf (∀ (λ H : El (fun (fun A B) (fun A B)), (⇒ (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (∀ (λ x : El A, (⇒ (∀ (λ z : El A, (⇒ (<< z x) (= (f z) (g z))))) (= (H f x) (H g x))))))))) (∃ (λ f : El (fun A B), (∀ (λ x : El A, (= (f x) (H f x)))))))));
