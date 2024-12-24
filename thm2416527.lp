require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416524_spec;
opaque symbol lem2416527 (b : El int) (a : El int) : Prf (= (int_mul a b) (int_mul b a)) ≔ ∧ₑ₁ (@lem2416524 (@el int) (@el int) (@el int) (@el int) b a (@el int) (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
