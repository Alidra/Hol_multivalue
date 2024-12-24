require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483485_term_abbrevs;
require open hol-light.thm1483483_spec;
opaque symbol lem1483485 (a : El real) (c : El real) (d : El real) (p : El num) (y : El real) (z : El real) (x : El real) (q : El num) : Prf (term0 a c d p y z x q) ≔ ∧ₑ₂ (@lem1483483 (@el real) a c d p y z x q);
