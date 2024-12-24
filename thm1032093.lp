require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032093_term_abbrevs;
require open hol-light.thm1032091_spec;
opaque symbol lem1032093 (b : El num) (a : El num) (c : El num) (d : El num) (p : El num) (y : El num) (z : El num) (x : El num) (q : El num) : Prf (term0 b a c d p y z x q) ≔ ∧ₑ₂ (@lem1032091 b a c d p y z x q);
