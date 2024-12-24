require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1195102 [A B] : Prf (∀ (λ f : El (fun A B), (= (∀ (λ l : El (list A), (∀ (λ m : El (list A), (⇒ (= ((@MAP A B) f l) ((@MAP A B) f m)) (= l m)))))) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (= (f x) (f y)) (= x y)))))))));
