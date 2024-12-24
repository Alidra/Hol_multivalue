require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm516558_term_abbrevs;
require open hol-light.thm124233_spec;
opaque symbol lem516557 : Prf term0 ≔ ∧ₑ₂ (@lem124233);
opaque symbol lem516558 (n : El num) : Prf (term1 n) ≔ (@lem516557) n;
