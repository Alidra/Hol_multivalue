require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1344310_term_abbrevs;
require open hol-light.thm1344307_spec;
opaque symbol lem1344309 : Prf term0 ≔ ∧ₑ₁ (@lem1344307);
opaque symbol lem1344310 (x : El real) : Prf (term1 x) ≔ (@lem1344309) x;
