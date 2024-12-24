require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1812_term_abbrevs;
require open hol-light.EXISTS_SIMP_spec;
opaque symbol lem1812 [A] (t : El bool) : Prf (term0 A t) ≔ (@lem1121 A) t;
