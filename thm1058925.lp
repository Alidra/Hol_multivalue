require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1058925_term_abbrevs;
require open hol-light.thm1058924_spec;
opaque symbol lem1058925 [A] : Prf (term0 A) ≔ ∧ₑ₂ (@lem1058924 A);
