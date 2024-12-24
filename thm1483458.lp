require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483458_term_abbrevs;
require open hol-light.thm1483455_spec;
opaque symbol lem1483458 (a : El real) : Prf (= (term0 a) term1) ≔ ∧ₑ₁ (@lem1483455 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
