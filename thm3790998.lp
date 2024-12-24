require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3790998_term_abbrevs;
require open hol-light.thm3790997_spec;
opaque symbol lem3790998 [A B] : Prf (term0 A B) ≔ ∧ₑ₂ (@lem3790997 A B);
