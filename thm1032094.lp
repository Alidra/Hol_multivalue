require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032094_term_abbrevs;
require open hol-light.thm1032091_spec;
opaque symbol lem1032094 (c : El num) (a : El num) (d : El num) : Prf (= (term0 a c d) (term0 c a d)) ≔ ∧ₑ₁ (@lem1032091 (@el num) a c d (@el num) (@el num) (@el num) (@el num) (@el num));
