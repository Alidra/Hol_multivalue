require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483436_term_abbrevs;
require open hol-light.thm1483434_spec;
opaque symbol lem1483436 (x : El real) : Prf (= (term0 x) x) ≔ ∧ₑ₁ (@lem1483434 (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) x (@el num));
