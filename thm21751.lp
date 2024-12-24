require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm21751_term_abbrevs;
require open hol-light.thm21750_spec;
opaque symbol lem21751 (t : El bool) : Prf (term0 t) ≔ ∧ₑ₂ (@lem21750 t);
