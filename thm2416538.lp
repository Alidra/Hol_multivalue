require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416538_term_abbrevs;
require open hol-light.thm2416536_spec;
opaque symbol lem2416538 (ly : El int) (rx : El int) (lx : El int) (ry : El int) (b : El int) (a : El int) (c : El int) (d : El int) (p : El num) (y : El int) (z : El int) (x : El int) (q : El num) : Prf (term0 ly rx lx ry b a c d p y z x q) ≔ ∧ₑ₂ (@lem2416536 ly rx lx ry b a c d p y z x q);
