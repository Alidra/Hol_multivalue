require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm513185_term_abbrevs;
require open hol-light.thm513141_spec;
opaque symbol lem513184 : Prf term0 ≔ ∧ₑ₂ (@lem513141);
opaque symbol lem513185 (n : El num) : Prf (term1 n) ≔ (@lem513184) n;
