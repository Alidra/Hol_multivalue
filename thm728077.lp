require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm728077_term_abbrevs;
require open hol-light.thm728071_spec;
opaque symbol lem728076 : Prf term0 ≔ ∧ₑ₁ (@lem728071);
opaque symbol lem728077 (n : El num) : Prf (term1 n) ≔ (@lem728076) n;
