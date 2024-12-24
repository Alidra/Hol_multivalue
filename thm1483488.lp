require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483485_spec;
opaque symbol lem1483488 (c : El real) (a : El real) : Prf (= (real_add a c) (real_add c a)) ≔ ∧ₑ₁ (@lem1483485 a c (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
