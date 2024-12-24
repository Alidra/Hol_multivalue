require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982737_term_abbrevs;
require open hol-light.thm1982734_spec;
opaque symbol lem1982737 (lx : El real) (rx : El real) (ly : El real) (ry : El real) : Prf (= (term0 lx ly rx ry) (term0 lx rx ly ry)) ≔ ∧ₑ₁ (@lem1982734 ly rx lx ry (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
