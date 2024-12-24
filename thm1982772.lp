require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982772_term_abbrevs;
require open hol-light.thm1982770_spec;
opaque symbol lem1982772 (p : El num) (y : El real) (z : El real) (x : El real) (q : El num) : Prf (term0 p y z x q) ≔ ∧ₑ₂ (@lem1982770 p y z x q);
