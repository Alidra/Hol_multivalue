require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982757_term_abbrevs;
require open hol-light.thm1982754_spec;
opaque symbol lem1982757 (c : El real) (a : El real) (d : El real) : Prf (= (term0 a c d) (term0 c a d)) ≔ ∧ₑ₁ (@lem1982754 (@el real) a c d (@el num) (@el real) (@el real) (@el real) (@el num));
