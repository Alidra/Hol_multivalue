require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem70373 : Prf (∃ (λ f : El (fun ind ind), (∃ (λ z : El ind, (∧ (∀ (λ x1 : El ind, (∀ (λ x2 : El ind, (= (= (f x1) (f x2)) (= x1 x2)))))) (∀ (λ x : El ind, (¬ (= (f x) z)))))))));
