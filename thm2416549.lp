require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416546_spec;
opaque symbol lem2416549 (rx : El int) (lx : El int) : Prf (= (int_mul lx rx) (int_mul rx lx)) ≔ ∧ₑ₁ (@lem2416546 rx lx (@el int) (@el int) (@el int) (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
