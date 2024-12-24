require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416558_term_abbrevs;
require open hol-light.thm2416556_spec;
opaque symbol lem2416558 (b : El int) (a : El int) (c : El int) (d : El int) (p : El num) (y : El int) (z : El int) (x : El int) (q : El num) : Prf (term0 b a c d p y z x q) ≔ ∧ₑ₂ (@lem2416556 b a c d p y z x q);
