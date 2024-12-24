require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7948706_spec;
opaque symbol lem7948708 : Prf (= ((@dimindex 1) (@UNIV 1)) (BIT1 _0)) ≔ ∧ₑ₂ (@lem7948706 bool (@el num));
