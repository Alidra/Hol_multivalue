require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982722_spec;
opaque symbol lem1982725 (b : El real) (a : El real) : Prf (= (real_mul a b) (real_mul b a)) ≔ ∧ₑ₁ (@lem1982722 (@el real) (@el real) (@el real) (@el real) b a (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
