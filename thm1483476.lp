require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483476_term_abbrevs;
require open hol-light.thm1483473_spec;
opaque symbol lem1483476 (lx : El real) (rx : El real) (ry : El real) : Prf (= (term0 lx rx ry) (term1 lx rx ry)) ≔ ∧ₑ₁ (@lem1483473 rx lx ry (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
