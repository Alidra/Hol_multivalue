require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416547_term_abbrevs;
require open hol-light.thm2416544_spec;
opaque symbol lem2416547 (lx : El int) (ly : El int) (rx : El int) : Prf (= (term0 lx ly rx) (term1 lx ly rx)) ≔ ∧ₑ₁ (@lem2416544 ly rx lx (@el int) (@el int) (@el int) (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
