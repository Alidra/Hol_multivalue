require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1365106_term_abbrevs;
require open hol-light.thm1365074_spec;
require open hol-light.thm1365083_spec;
opaque symbol lem1365106 : Prf term0 ≔ ∧ᵢ (@lem1365074) (@lem1365083);
