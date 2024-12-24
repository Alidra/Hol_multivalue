require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FINITE_INDUCT_term_abbrevs;
require open hol-light.thm3197564_spec;
opaque symbol lem3197567 [A] : Prf (term0 A) ≔ ∧ₑ₁ (@lem3197564 A);
