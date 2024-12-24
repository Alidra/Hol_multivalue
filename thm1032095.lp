require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032095_term_abbrevs;
require open hol-light.thm1032093_spec;
opaque symbol lem1032095 (a : El num) (c : El num) (d : El num) (p : El num) (y : El num) (z : El num) (x : El num) (q : El num) : Prf (term0 a c d p y z x q) ≔ ∧ₑ₂ (@lem1032093 (@el num) a c d p y z x q);
