require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2318496_term_abbrevs;
require open hol-light.thm2318495_spec;
opaque symbol lem2318496 (x : El int) (y : El int) : Prf (term0 x y) ≔ ∧ₑ₂ (@lem2318495 x y);
