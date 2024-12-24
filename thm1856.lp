require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1856_term_abbrevs;
require open hol-light.thm1855_spec;
opaque symbol lem1856 (t : El bool) : Prf (term0 t) ≔ ∧ₑ₂ (@lem1855 t);
