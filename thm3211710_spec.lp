require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3211710 [A] (s : El (fun A bool)) (t : El (fun A bool)) (x : El A) : Prf ((λ x' : El A, (= ((@IN A) x' ((@INTER A) s t)) (∧ ((@IN A) x' s) ((@IN A) x' t)))) x);
