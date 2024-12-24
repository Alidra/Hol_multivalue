require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1199951 [A B] : Prf (∀ (λ f : El (fun A B), (= (∀ (λ m : El (list B), (∃ (λ l : El (list A), (= ((@MAP A B) f l) m))))) (∀ (λ y : El B, (∃ (λ x : El A, (= (f x) y))))))));
