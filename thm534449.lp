require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm534449_term_abbrevs;
require open hol-light.thm534447_spec;
opaque symbol lem534448 : Prf term0 ≔ ∧ₑ₂ (@lem534447);
opaque symbol lem534449 (n : El num) : Prf (term1 n) ≔ (@lem534448) n;
