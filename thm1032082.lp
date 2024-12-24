require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032082_term_abbrevs;
require open hol-light.thm1032079_spec;
opaque symbol lem1032082 (lx : El num) (ly : El num) (rx : El num) : Prf (= (term0 lx ly rx) (term1 lx ly rx)) ≔ ∧ₑ₁ (@lem1032079 ly rx lx (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num));
