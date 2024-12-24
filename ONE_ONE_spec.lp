require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem68585 [A B] : Prf (∀ (λ f : El (fun A B), (= ((@ONE_ONE A B) f) (∀ (λ x1 : El A, (∀ (λ x2 : El A, (⇒ (= (f x1) (f x2)) (= x1 x2)))))))));
