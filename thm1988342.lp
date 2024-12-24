require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1988342_term_abbrevs;
require open hol-light.thm1988340_spec;
opaque symbol lem1988342 (x : El real) (y : El real) : Prf (term0 x y) ≔ ∧ₑ₂ (@lem1988340 x y);
