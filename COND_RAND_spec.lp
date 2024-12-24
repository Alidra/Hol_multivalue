require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem12958 [A B] : Prf (∀ (λ b : El bool, (∀ (λ f : El (fun A B), (∀ (λ x : El A, (∀ (λ y : El A, (= (f ((@COND A) b x y)) ((@COND B) b (f x) (f y)))))))))));
