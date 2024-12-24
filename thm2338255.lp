require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2338255_term_abbrevs;
require open hol-light.NOT_FORALL_THM_spec;
opaque symbol lem2338255 [A] (P : El (fun A bool)) : Prf (term0 A P) ≔ (@lem10884 A) P;
