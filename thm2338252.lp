require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2338252_term_abbrevs;
require open hol-light.num_WOP_spec;
opaque symbol lem2338252 (P : El (fun num bool)) : Prf (term0 P) ≔ (@lem116994) P;
