require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm728073_term_abbrevs;
require open hol-light.thm728071_spec;
opaque symbol lem728072 : Prf term0 ≔ ∧ₑ₂ (@lem728071);
opaque symbol lem728073 (n : El num) : Prf (term1 n) ≔ (@lem728072) n;
