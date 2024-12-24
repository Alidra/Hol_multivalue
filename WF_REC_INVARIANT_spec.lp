require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem339113 [A B] (<< : El (fun A (fun A bool))) : Prf (⇒ ((@WF A) <<) (∀ (λ H : El (fun (fun A B) (fun A B)), (∀ (λ S : El (fun A (fun B bool)), (⇒ (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (∀ (λ x : El A, (⇒ (∀ (λ z : El A, (⇒ (<< z x) (∧ (= (f z) (g z)) (S z (f z)))))) (∧ (= (H f x) (H g x)) (S x (H f x)))))))))) (∃ (λ f : El (fun A B), (∀ (λ x : El A, (= (f x) (H f x))))))))))));
