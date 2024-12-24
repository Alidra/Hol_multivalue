require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3195125 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@PSUBSET A) s t) (∧ ((@SUBSET A) s t) (¬ (= s t))))))));
