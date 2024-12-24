require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982758_spec;
opaque symbol lem1982761 (c : El real) (a : El real) : Prf (= (real_add a c) (real_add c a)) ≔ ∧ₑ₁ (@lem1982758 a c (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
