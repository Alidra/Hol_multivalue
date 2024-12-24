require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3197565 [A] : Prf (∧ ((@FINITE A) (@EMPTY A)) (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) ((@FINITE A) ((@INSERT A) x s))))))));
