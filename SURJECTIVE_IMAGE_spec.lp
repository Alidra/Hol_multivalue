require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5042894 [A B] : Prf (∀ (λ f : El (fun A B), (= (∀ (λ t : El (fun B bool), (∃ (λ s : El (fun A bool), (= ((@IMAGE A B) f s) t))))) (∀ (λ y : El B, (∃ (λ x : El A, (= (f x) y))))))));
