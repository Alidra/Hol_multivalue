require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416571_term_abbrevs;
require open hol-light.thm2416568_spec;
opaque symbol lem2416571 (x : El int) (q : El num) : Prf (= (term0 q x) (term1 x q)) ≔ ∧ₑ₁ (@lem2416568 (@el num) (@el int) (@el int) x q);
