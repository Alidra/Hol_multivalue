require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416545_term_abbrevs;
require open hol-light.thm2416542_spec;
opaque symbol lem2416545 (lx : El int) (rx : El int) (ly : El int) : Prf (= (term0 lx ly rx) (term0 lx rx ly)) ≔ ∧ₑ₁ (@lem2416542 ly rx lx (@el int) (@el int) (@el int) (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
