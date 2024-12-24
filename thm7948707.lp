require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7948704_spec;
opaque symbol lem7948707 [A] (n : El num) : Prf (= (= ((@dimindex A) (@UNIV A)) n) (= ((@dimindex (tybit0 A)) (@UNIV (tybit0 A))) (BIT0 n))) ≔ ∧ₑ₁ (@lem7948704 A n);
