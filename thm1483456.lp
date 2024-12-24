require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483456_term_abbrevs;
require open hol-light.thm1483453_spec;
opaque symbol lem1483456 (a : El real) : Prf (= (term0 a) term1) ≔ ∧ₑ₁ (@lem1483453 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
