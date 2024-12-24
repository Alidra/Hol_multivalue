require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416519_term_abbrevs;
require open hol-light.thm2416516_spec;
opaque symbol lem2416519 (m : El int) : Prf (= (int_add m m) (term0 m)) ≔ ∧ₑ₁ (@lem2416516 m (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
