require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9396 [A] (P : El (fun A bool)) : Prf (⇒ (∃ P) (P ((@ε A) P)));
