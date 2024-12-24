require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3315830 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@PSUBSET A) s t) (∃ (λ x : El A, (∧ (¬ ((@IN A) x s)) ((@SUBSET A) ((@INSERT A) x s) t)))))))));
