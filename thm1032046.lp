require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032046_term_abbrevs;
require open hol-light.thm1032044_spec;
opaque symbol lem1032046 (x : El num) : Prf (= (term0 x) x) ≔ ∧ₑ₁ (@lem1032044 (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) x (@el num));
