require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9127 [A B] (t : El (fun A B)) : Prf (= (λ x : El A, (t x)) t);
