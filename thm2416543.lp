require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416543_term_abbrevs;
require open hol-light.thm2416540_spec;
opaque symbol lem2416543 (rx : El int) (lx : El int) (ly : El int) (ry : El int) : Prf (= (term0 lx ly rx ry) (term1 rx lx ly ry)) ≔ ∧ₑ₁ (@lem2416540 ly rx lx ry (@el int) (@el int) (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
