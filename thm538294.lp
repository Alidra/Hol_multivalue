require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm538294_term_abbrevs;
require open hol-light.thm538261_spec;
opaque symbol lem538293 : Prf term0 ≔ ∧ₑ₁ (@lem538261);
opaque symbol lem538294 (n : El num) : Prf (term1 n) ≔ (@lem538293) n;
