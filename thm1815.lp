require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1815_term_abbrevs;
require open hol-light.FORALL_SIMP_spec;
opaque symbol lem1815 [A] (t : El bool) : Prf (term0 A t) ≔ (@lem1096 A) t;
