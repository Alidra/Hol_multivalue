require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3206137 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (= ((@IN A) x ((@REST A) s)) (∧ ((@IN A) x s) (¬ (= x ((@CHOICE A) s)))))))));
