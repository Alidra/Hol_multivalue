require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1980011_term_abbrevs;
require open hol-light.thm1980010_spec;
opaque symbol lem1980011 (x : El num) (y : El num) : Prf (term0 x y) ≔ ∧ₑ₂ (@lem1980010 x y);
