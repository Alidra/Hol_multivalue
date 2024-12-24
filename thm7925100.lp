require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7925100_term_abbrevs;
require open hol-light.thm7925098_spec;
opaque symbol lem7925100 [A] (tybit0' : El (type1331 A)) (_103783' : El (type45 A)) (h1 : Prf (= tybit0' (term0 A _103783'))) : Prf (term1 A tybit0' _103783') ≔ ∧ₑ₁ (@lem7925098 A tybit0' _103783' h1);
