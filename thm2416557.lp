require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416557_term_abbrevs;
require open hol-light.thm2416554_spec;
opaque symbol lem2416557 (a : El int) (b : El int) (c : El int) : Prf (= (term0 a b c) (term1 a b c)) ≔ ∧ₑ₁ (@lem2416554 b a c (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
