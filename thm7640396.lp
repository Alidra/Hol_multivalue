require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7640394_spec;
opaque symbol lem7640396 [M N] : Prf ((@FINITE (finite_sum M N)) (@UNIV (finite_sum M N))) ≔ ∧ₑ₁ (@lem7640394 M N);
