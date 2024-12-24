require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1099511_term_abbrevs;
require open hol-light.thm1099508_spec;
opaque symbol lem1099510 [_25272] : Prf (term0 _25272) ≔ ∧ₑ₁ (@lem1099508 _25272);
opaque symbol lem1099511 [_25272] (x : El _25272) : Prf (term1 _25272 x) ≔ (@lem1099510 _25272) x;
