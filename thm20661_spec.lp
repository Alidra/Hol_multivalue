require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20661 [A B] (f : El (fun A B)) (x : El A) : Prf ((λ x' : El A, (= (f x') ((@I (fun A B)) f x'))) x);
