require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm18394_term_abbrevs;
require open hol-light.thm18004_spec;
require open hol-light.thm18065_spec;
opaque symbol lem18394 [A] (P : El (fun A bool)) : Prf (= (term0 A P) (term1 A P)) ≔ EQ_MP (@lem18004 A P) (@lem18065 A P);
