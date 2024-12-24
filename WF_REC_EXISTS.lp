require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.WF_REC_EXISTS_term_abbrevs;
require open hol-light.thm358361_spec;
opaque symbol lem358362 [A B] (<< : El (type1402 A)) : Prf (term0 A B <<) ≔ λ h0 : Prf ((@WF A) <<), (@lem358361 A B << h0);
