require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483440_term_abbrevs;
require open hol-light.thm1483437_spec;
opaque symbol lem1483440 (a : El real) (m : El real) : Prf (= (term0 a m) (term1 a m)) ≔ ∧ₑ₁ (@lem1483437 m (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
