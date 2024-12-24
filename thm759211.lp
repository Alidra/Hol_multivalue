require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm759211_term_abbrevs;
require open hol-light.thm759205_spec;
opaque symbol lem759210 : Prf term0 ≔ ∧ₑ₁ (@lem759205);
opaque symbol lem759211 (n : El num) : Prf (term1 n) ≔ (@lem759210) n;
