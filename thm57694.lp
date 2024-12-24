require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm57694_term_abbrevs;
require open hol-light.LET_END_DEF_spec;
opaque symbol lem57694 [A] (t : El A) : Prf (term0 A t) ≔ (@lem44139 A) t;
