require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416511_term_abbrevs;
require open hol-light.thm2416509_spec;
opaque symbol lem2416511 (x : El int) : Prf (= (term0 x) x) ≔ ∧ₑ₁ (@lem2416509 (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el num) (@el int) (@el int) x (@el num));
