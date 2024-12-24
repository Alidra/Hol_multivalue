require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982768_term_abbrevs;
require open hol-light.thm1982766_spec;
opaque symbol lem1982768 (p : El num) (y : El real) (z : El real) (x : El real) (q : El num) : Prf (term0 p y z x q) ≔ ∧ₑ₂ (@lem1982766 p y z x q);
