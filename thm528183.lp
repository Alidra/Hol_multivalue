require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm528183_term_abbrevs;
require open hol-light.thm528181_spec;
opaque symbol lem528182 : Prf term0 ≔ ∧ₑ₂ (@lem528181);
opaque symbol lem528183 (n : El num) : Prf (term1 n) ≔ (@lem528182) n;
