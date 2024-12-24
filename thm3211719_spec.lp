require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3211719 [A] (s : El (fun A bool)) (t : El (fun A bool)) (x : El A) : Prf ((λ x' : El A, (= ((@IN A) x' ((@UNION A) s t)) (∨ ((@IN A) x' s) ((@IN A) x' t)))) x);
