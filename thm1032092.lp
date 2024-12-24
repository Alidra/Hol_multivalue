require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032092_term_abbrevs;
require open hol-light.thm1032089_spec;
opaque symbol lem1032092 (a : El num) (b : El num) (c : El num) : Prf (= (term0 a b c) (term1 a b c)) ≔ ∧ₑ₁ (@lem1032089 b a c (@el num) (@el num) (@el num) (@el num) (@el num) (@el num));
