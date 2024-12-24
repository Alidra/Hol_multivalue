require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm546169_term_abbrevs;
require open hol-light.thm546167_spec;
opaque symbol lem546168 : Prf term0 ≔ ∧ₑ₂ (@lem546167);
opaque symbol lem546169 (n : El num) : Prf (term1 n) ≔ (@lem546168) n;
