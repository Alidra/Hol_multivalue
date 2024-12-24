require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1834_term_abbrevs;
require open hol-light.thm1833_spec;
opaque symbol lem1834 (t : El bool) : Prf (term0 t) ≔ ∧ₑ₂ (@lem1833 t);
