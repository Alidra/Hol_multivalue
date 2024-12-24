require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483466_term_abbrevs;
require open hol-light.thm1483463_spec;
opaque symbol lem1483466 (lx : El real) (ly : El real) (rx : El real) (ry : El real) : Prf (= (term0 lx ly rx ry) (term1 lx ly rx ry)) ≔ ∧ₑ₁ (@lem1483463 ly rx lx ry (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
