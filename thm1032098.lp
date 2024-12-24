require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032095_spec;
opaque symbol lem1032098 (c : El num) (a : El num) : Prf (= (+ a c) (+ c a)) ≔ ∧ₑ₁ (@lem1032095 a c (@el num) (@el num) (@el num) (@el num) (@el num) (@el num));
