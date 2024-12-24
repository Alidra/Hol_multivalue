require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm18392_term_abbrevs;
require open hol-light.thm17991_spec;
require open hol-light.thm18041_spec;
opaque symbol lem18392 [A] (P : El (fun A bool)) : Prf (= (term0 A P) (term1 A P)) ≔ EQ_MP (@lem17991 A P) (@lem18041 A P);
