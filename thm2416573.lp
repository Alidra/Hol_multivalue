require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416573_term_abbrevs;
require open hol-light.thm2416570_spec;
opaque symbol lem2416573 (x : El int) : Prf (= (int_mul x x) (term0 x)) ≔ ∧ₑ₁ (@lem2416570 (@el num) (@el int) (@el int) x (@el num));
