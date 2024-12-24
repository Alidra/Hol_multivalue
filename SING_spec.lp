require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3197081 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@SING A) s) (∃ (λ x : El A, (= s ((@INSERT A) x (@EMPTY A))))))));
