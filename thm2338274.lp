require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2338274_term_abbrevs;
require open hol-light.thm2338267_spec;
opaque symbol lem2338274 (P : El (fun int bool)) : Prf (term0 P) ≔ (@lem2338267) P;
