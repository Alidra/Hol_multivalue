require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1988320_term_abbrevs;
require open hol-light.thm1396686_spec;
opaque symbol lem1988320 (x : El real) (y : El real) : Prf (term0 x y) ≔ ∧ₑ₂ (@lem1396686 x y);
