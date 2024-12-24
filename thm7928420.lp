require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7928420_term_abbrevs;
require open hol-light.thm7928418_spec;
opaque symbol lem7928420 [A] (tybit1' : El (type1329 A)) (_103802' : El (type39 A)) (h1 : Prf (= tybit1' (term0 A _103802'))) : Prf (term1 A _103802' tybit1') ≔ ∧ₑ₁ (@lem7928418 A tybit1' _103802' h1);
