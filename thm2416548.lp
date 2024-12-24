require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416548_term_abbrevs;
require open hol-light.thm2416546_spec;
opaque symbol lem2416548 (rx : El int) (lx : El int) (ry : El int) (b : El int) (a : El int) (c : El int) (d : El int) (p : El num) (y : El int) (z : El int) (x : El int) (q : El num) : Prf (term0 rx lx ry b a c d p y z x q) ≔ ∧ₑ₂ (@lem2416546 rx lx ry b a c d p y z x q);
