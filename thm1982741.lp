require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982741_term_abbrevs;
require open hol-light.thm1982738_spec;
opaque symbol lem1982741 (rx : El real) (lx : El real) (ly : El real) (ry : El real) : Prf (= (term0 lx ly rx ry) (term1 rx lx ly ry)) ≔ ∧ₑ₁ (@lem1982738 ly rx lx ry (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
