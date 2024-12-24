require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3203700 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@CHOICE A) s) ((@ε A) (λ x : El A, ((@IN A) x s))))));
