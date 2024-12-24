require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416565_term_abbrevs;
require open hol-light.thm2416562_spec;
opaque symbol lem2416565 (a : El int) (c : El int) (d : El int) : Prf (= (term0 a c d) (term1 a c d)) ≔ ∧ₑ₁ (@lem2416562 a c d (@el num) (@el int) (@el int) (@el int) (@el num));
