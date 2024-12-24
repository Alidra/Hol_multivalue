require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416561_term_abbrevs;
require open hol-light.thm2416558_spec;
opaque symbol lem2416561 (a : El int) (c : El int) (b : El int) : Prf (= (term0 a b c) (term0 a c b)) ≔ ∧ₑ₁ (@lem2416558 b a c (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
