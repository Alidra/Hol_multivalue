require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416515_term_abbrevs;
require open hol-light.thm2416512_spec;
opaque symbol lem2416515 (a : El int) (m : El int) : Prf (= (term0 a m) (term1 a m)) ≔ ∧ₑ₁ (@lem2416512 m (@el int) (@el int) (@el int) (@el int) (@el int) a (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
