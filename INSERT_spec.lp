require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3192218 [A] (s : El (fun A bool)) (x : El A) : Prf (= ((@INSERT A) x s) ((@GSPEC A) (λ GEN_PVAR_5 : El A, (∃ (λ y : El A, ((@SETSPEC A) GEN_PVAR_5 (∨ ((@IN A) y s) (= y x)) y))))));
