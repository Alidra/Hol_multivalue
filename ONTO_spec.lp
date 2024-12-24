require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem68752 [A B] : Prf (∀ (λ f : El (fun A B), (= ((@ONTO A B) f) (∀ (λ y : El B, (∃ (λ x : El A, (= y (f x)))))))));
