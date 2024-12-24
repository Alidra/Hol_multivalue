require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm534498_term_abbrevs;
require open hol-light.thm534465_spec;
opaque symbol lem534497 : Prf term0 ≔ ∧ₑ₁ (@lem534465);
opaque symbol lem534498 (n : El num) : Prf (term1 n) ≔ (@lem534497) n;
