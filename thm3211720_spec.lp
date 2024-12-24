require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3211720 [A] (s : El (fun A bool)) (x : El A) (t : El (fun A bool)) : Prf (= ((λ x' : El A, (= ((@IN A) x' ((@UNION A) s t)) (∨ ((@IN A) x' s) ((@IN A) x' t)))) x) (= ((@IN A) x ((@UNION A) s t)) (∨ ((@IN A) x s) ((@IN A) x t))));
