require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7936861_term_abbrevs;
require open hol-light.DIMINDEX_CLAUSES_spec;
opaque symbol lem7936861 [A] : Prf (term0 A) ≔ ∧ₑ₂ (@lem7933204 A);
