require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416521_term_abbrevs;
require open hol-light.thm2416518_spec;
opaque symbol lem2416521 (m : El int) : Prf (= (term0 m) term1) ≔ ∧ₑ₁ (@lem2416518 m (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
