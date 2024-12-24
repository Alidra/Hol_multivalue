require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416551_term_abbrevs;
require open hol-light.thm2416548_spec;
opaque symbol lem2416551 (lx : El int) (rx : El int) (ry : El int) : Prf (= (term0 lx rx ry) (term1 lx rx ry)) ≔ ∧ₑ₁ (@lem2416548 rx lx ry (@el int) (@el int) (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
