require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1988326_term_abbrevs;
require open hol-light.thm1988324_spec;
opaque symbol lem1988326 (x : El real) (y : El real) : Prf (term0 x y) ≔ ∧ₑ₂ (@lem1988324 x y);
