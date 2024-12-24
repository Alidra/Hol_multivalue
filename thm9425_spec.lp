require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9425 [A] (P : El (fun A bool)) : Prf (= (P ((@ε A) P)) (∃ P));
