require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483471_spec;
opaque symbol lem1483474 (rx : El real) (lx : El real) : Prf (= (real_mul lx rx) (real_mul rx lx)) ≔ ∧ₑ₁ (@lem1483471 rx lx (@el real) (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
