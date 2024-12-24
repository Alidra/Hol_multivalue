require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1367253_term_abbrevs;
require open hol-light.thm1367111_spec;
opaque symbol lem1367253 (x : El num) : Prf (term0 x) ≔ ∧ₑ₂ (@lem1367111 x);
