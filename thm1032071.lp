require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032071_term_abbrevs;
require open hol-light.thm1032069_spec;
opaque symbol lem1032071 (ly : El num) (rx : El num) (lx : El num) (ry : El num) (b : El num) (a : El num) (c : El num) (d : El num) (p : El num) (y : El num) (z : El num) (x : El num) (q : El num) : Prf (term0 ly rx lx ry b a c d p y z x q) ≔ ∧ₑ₂ (@lem1032069 ly rx lx ry b a c d p y z x q);
