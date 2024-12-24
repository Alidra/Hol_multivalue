require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1809 [A B] (f : El (fun A B)) (y : El A) : Prf ((λ y' : El A, (= ((λ x : El A, (f x)) y') (f y'))) y);
