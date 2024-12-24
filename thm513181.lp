require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm513181_term_abbrevs;
require open hol-light.thm513125_spec;
opaque symbol lem513180 : Prf term0 ≔ ∧ₑ₁ (@lem513125);
opaque symbol lem513181 (n : El num) : Prf (term1 n) ≔ (@lem513180) n;
