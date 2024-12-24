require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982739_term_abbrevs;
require open hol-light.thm1982736_spec;
opaque symbol lem1982739 (lx : El real) (ly : El real) (rx : El real) (ry : El real) : Prf (= (term0 lx ly rx ry) (term1 lx ly rx ry)) ≔ ∧ₑ₁ (@lem1982736 ly rx lx ry (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
