require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm21384_spec;
opaque symbol lem21386 [A] (x : El A) : Prf (= x x) ≔ ∧ₑ₁ (@lem21384 A x (@el A) (@el A));
