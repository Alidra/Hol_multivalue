require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3608316 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ x : El A, (= ((@FINITE A) ((@INSERT A) x s)) ((@FINITE A) s))))));
