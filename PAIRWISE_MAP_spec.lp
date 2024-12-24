require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1231297 [A B] : Prf (∀ (λ R : El (fun B (fun B bool)), (∀ (λ f : El (fun A B), (∀ (λ l : El (list A), (= ((@PAIRWISE B) R ((@MAP A B) f l)) ((@PAIRWISE A) (λ x : El A, (λ y : El A, (R (f x) (f y)))) l))))))));
