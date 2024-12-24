require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416553_term_abbrevs;
require open hol-light.thm2416550_spec;
opaque symbol lem2416553 (rx : El int) (lx : El int) (ry : El int) : Prf (= (term0 lx rx ry) (term0 rx lx ry)) ≔ ∧ₑ₁ (@lem2416550 rx lx ry (@el int) (@el int) (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
