require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982743_term_abbrevs;
require open hol-light.thm1982740_spec;
opaque symbol lem1982743 (lx : El real) (rx : El real) (ly : El real) : Prf (= (term0 lx ly rx) (term0 lx rx ly)) ≔ ∧ₑ₁ (@lem1982740 ly rx lx (@el real) (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
