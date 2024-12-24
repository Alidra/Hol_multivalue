require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.WF_REC_term_abbrevs;
require open hol-light.thm339314_spec;
opaque symbol lem339315 [A B] (<< : El (type1402 A)) : Prf (term0 A B <<) ≔ λ h0 : Prf ((@WF A) <<), (@lem339314 A B << h0);
