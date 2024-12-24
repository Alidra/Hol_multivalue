require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032059_spec;
opaque symbol lem1032062 (b : El num) (a : El num) : Prf (= (* a b) (* b a)) ≔ ∧ₑ₁ (@lem1032059 (@el num) (@el num) (@el num) (@el num) b a (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num));
