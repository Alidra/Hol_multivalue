require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem44133 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ x : El A, (= ((@LET A B) f x) (f x))))));
