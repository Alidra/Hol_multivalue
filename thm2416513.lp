require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416513_term_abbrevs;
require open hol-light.thm2416510_spec;
opaque symbol lem2416513 (a : El int) (b : El int) (m : El int) : Prf (= (term0 a b m) (term1 a b m)) ≔ ∧ₑ₁ (@lem2416510 m (@el int) (@el int) (@el int) (@el int) b a (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
