require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3183080 [A] (P : El (fun A bool)) (x : El A) : Prf ((λ x' : El A, (= ((@IN A) x' P) (P x'))) x);
