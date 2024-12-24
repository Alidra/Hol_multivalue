require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem13156 [A B] : Prf (∀ (λ b : El bool, (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (= (λ x : El A, ((@COND B) b (f x) (g x))) ((@COND (fun A B)) b f g))))))));
