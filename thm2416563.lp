require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416560_spec;
opaque symbol lem2416563 (c : El int) (a : El int) : Prf (= (int_add a c) (int_add c a)) ≔ ∧ₑ₁ (@lem2416560 a c (@el int) (@el num) (@el int) (@el int) (@el int) (@el num));
