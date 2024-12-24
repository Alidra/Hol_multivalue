require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.WF_REC_INVARIANT_term_abbrevs;
require open hol-light.thm322939_spec;
require open hol-light.thm339112_spec;
opaque symbol lem339113 [A B] (<< : El (type1402 A)) : Prf (term0 A B <<) ≔ EQ_MP (@lem322939 A B <<) (@lem339112 A B <<);
