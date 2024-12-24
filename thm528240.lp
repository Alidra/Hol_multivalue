require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm528240_term_abbrevs;
require open hol-light.thm528197_spec;
opaque symbol lem528239 : Prf term0 ≔ ∧ₑ₁ (@lem528197);
opaque symbol lem528240 (n : El num) : Prf (term1 n) ≔ (@lem528239) n;
