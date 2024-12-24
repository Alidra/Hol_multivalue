require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3205803 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ x : El A, (∀ (λ y : El A, (= ((@IN A) x ((@DELETE A) s y)) (∧ ((@IN A) x s) (¬ (= x y))))))))));
