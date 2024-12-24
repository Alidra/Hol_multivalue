require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm21742_term_abbrevs;
require open hol-light.thm21741_spec;
opaque symbol lem21742 (t : El bool) : Prf (term0 t) ≔ ∧ₑ₂ (@lem21741 t);
