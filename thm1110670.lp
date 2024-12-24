require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1110670_term_abbrevs;
require open hol-light.thm1110669_spec;
opaque symbol lem1110670 [A] : Prf (term0 A) ≔ ∧ₑ₂ (@lem1110669 A);
