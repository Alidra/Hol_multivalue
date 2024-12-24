require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483473_term_abbrevs;
require open hol-light.thm1483471_spec;
opaque symbol lem1483473 (rx : El real) (lx : El real) (ry : El real) (b : El real) (a : El real) (c : El real) (d : El real) (p : El num) (y : El real) (z : El real) (x : El real) (q : El num) : Prf (term0 rx lx ry b a c d p y z x q) ≔ ∧ₑ₂ (@lem1483471 rx lx ry b a c d p y z x q);
