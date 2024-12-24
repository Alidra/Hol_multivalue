require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982774_term_abbrevs;
require open hol-light.thm1982772_spec;
opaque symbol lem1982774 (y : El real) (z : El real) (x : El real) (q : El num) : Prf (term0 y z x q) ≔ ∧ₑ₂ (@lem1982772 (@el num) y z x q);
