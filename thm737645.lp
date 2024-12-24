require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm737645_term_abbrevs;
require open hol-light.thm737643_spec;
opaque symbol lem737644 : Prf term0 ≔ ∧ₑ₂ (@lem737643);
opaque symbol lem737645 (n : El num) : Prf (term1 n) ≔ (@lem737644) n;
