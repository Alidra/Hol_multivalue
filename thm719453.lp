require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm719453_term_abbrevs;
require open hol-light.thm719451_spec;
opaque symbol lem719452 : Prf term0 ≔ ∧ₑ₂ (@lem719451);
opaque symbol lem719453 (n : El num) : Prf (term1 n) ≔ (@lem719452) n;
