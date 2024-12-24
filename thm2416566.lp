require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416566_term_abbrevs;
require open hol-light.thm2416564_spec;
opaque symbol lem2416566 (p : El num) (y : El int) (z : El int) (x : El int) (q : El num) : Prf (term0 p y z x q) ≔ ∧ₑ₂ (@lem2416564 p y z x q);
