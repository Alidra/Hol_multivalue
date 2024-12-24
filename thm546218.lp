require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm546218_term_abbrevs;
require open hol-light.thm546185_spec;
opaque symbol lem546217 : Prf term0 ≔ ∧ₑ₁ (@lem546185);
opaque symbol lem546218 (n : El num) : Prf (term1 n) ≔ (@lem546217) n;
