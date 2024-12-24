require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem358361 [A B] (<< : El (fun A (fun A bool))) (h1 : Prf ((@WF A) <<)) : Prf (∀ (λ P : El (fun (fun A B) (fun A (fun B bool))), (⇒ (∧ (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (∀ (λ x : El A, (∀ (λ y : El B, (⇒ (∀ (λ z : El A, (⇒ (<< z x) (= (f z) (g z))))) (= (P f x y) (P g x y))))))))))) (∀ (λ f : El (fun A B), (∀ (λ x : El A, (⇒ (∀ (λ z : El A, (⇒ (<< z x) (P f z (f z))))) (∃ (λ y : El B, (P f x y))))))))) (∃ (λ f : El (fun A B), (∀ (λ x : El A, (P f x (f x)))))))));
