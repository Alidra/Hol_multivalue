require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483490_term_abbrevs;
require open hol-light.thm1483487_spec;
opaque symbol lem1483490 (a : El real) (c : El real) (d : El real) : Prf (= (term0 a c d) (term1 a c d)) ≔ ∧ₑ₁ (@lem1483487 a c d (@el num) (@el real) (@el real) (@el real) (@el num));
