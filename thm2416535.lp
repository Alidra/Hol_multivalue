require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416535_term_abbrevs;
require open hol-light.thm2416532_spec;
opaque symbol lem2416535 (a : El int) : Prf (= (term0 a) a) ≔ ∧ₑ₁ (@lem2416532 (@el int) (@el int) (@el int) (@el int) (@el int) a (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
