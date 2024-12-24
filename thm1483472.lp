require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483472_term_abbrevs;
require open hol-light.thm1483469_spec;
opaque symbol lem1483472 (lx : El real) (ly : El real) (rx : El real) : Prf (= (term0 lx ly rx) (term1 lx ly rx)) ≔ ∧ₑ₁ (@lem1483469 ly rx lx (@el real) (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
