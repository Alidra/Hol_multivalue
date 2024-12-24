require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm528154_term_abbrevs;
require open hol-light.thm528111_spec;
opaque symbol lem528153 : Prf term0 ≔ ∧ₑ₁ (@lem528111);
opaque symbol lem528154 (n : El num) : Prf (term1 n) ≔ (@lem528153) n;
