require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416523_term_abbrevs;
require open hol-light.thm2416520_spec;
opaque symbol lem2416523 (a : El int) : Prf (= (term0 a) a) ≔ ∧ₑ₁ (@lem2416520 (@el int) (@el int) (@el int) (@el int) (@el int) a (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
