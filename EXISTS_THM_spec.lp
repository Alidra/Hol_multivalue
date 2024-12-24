require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9307 [A] : Prf (= (@∃ A) (λ P : El (fun A bool), (P ((@ε A) P))));
