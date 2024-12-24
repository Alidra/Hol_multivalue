require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483556_term_abbrevs;
require open hol-light.thm1396686_spec;
opaque symbol lem1483556 (x : El real) (y : El real) : Prf (term0 x y) ≔ ∧ₑ₂ (@lem1396686 x y);
