require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483484_term_abbrevs;
require open hol-light.thm1483481_spec;
opaque symbol lem1483484 (c : El real) (a : El real) (d : El real) : Prf (= (term0 a c d) (term0 c a d)) ≔ ∧ₑ₁ (@lem1483481 (@el real) a c d (@el num) (@el real) (@el real) (@el real) (@el num));
