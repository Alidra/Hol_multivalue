require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7948706_spec;
opaque symbol lem7948709 [A] (n : El num) : Prf (= (= ((@dimindex A) (@UNIV A)) n) (= ((@dimindex (tybit1 A)) (@UNIV (tybit1 A))) (BIT1 n))) ≔ ∧ₑ₁ (@lem7948706 A n);
