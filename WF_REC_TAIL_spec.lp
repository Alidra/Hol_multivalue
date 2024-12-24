require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem403968 [A B] : Prf (∀ (λ P : El (fun A bool), (∀ (λ g : El (fun A A), (∀ (λ h : El (fun A B), (∃ (λ f : El (fun A B), (∀ (λ x : El A, (= (f x) ((@COND B) (P x) (f (g x)) (h x)))))))))))));
