require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416559_term_abbrevs;
require open hol-light.thm2416556_spec;
opaque symbol lem2416559 (c : El int) (a : El int) (d : El int) : Prf (= (term0 a c d) (term0 c a d)) ≔ ∧ₑ₁ (@lem2416556 (@el int) a c d (@el num) (@el int) (@el int) (@el int) (@el num));
