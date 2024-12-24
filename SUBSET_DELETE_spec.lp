require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3310605 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@SUBSET A) s ((@DELETE A) t x)) (∧ (¬ ((@IN A) x s)) ((@SUBSET A) s t)))))))));
