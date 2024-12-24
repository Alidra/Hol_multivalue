require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1822_term_abbrevs;
require open hol-light.thm1821_spec;
opaque symbol lem1822 (t : El bool) : Prf (term0 t) ≔ ∧ₑ₂ (@lem1821 t);
