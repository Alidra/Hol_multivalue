require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416541_term_abbrevs;
require open hol-light.thm2416538_spec;
opaque symbol lem2416541 (lx : El int) (ly : El int) (rx : El int) (ry : El int) : Prf (= (term0 lx ly rx ry) (term1 lx ly rx ry)) ≔ ∧ₑ₁ (@lem2416538 ly rx lx ry (@el int) (@el int) (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
