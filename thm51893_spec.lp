require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem51893 [A B] (f : El (fun A B)) (g : El (fun A B)) : Prf (= ((λ g' : El (fun A B), (= (= f g') (∀ (λ x : El A, (= (f x) (g' x)))))) g) (= (= f g) (∀ (λ x : El A, (= (f x) (g x))))));
