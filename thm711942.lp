require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm711942_term_abbrevs;
require open hol-light.thm711940_spec;
opaque symbol lem711941 : Prf term0 ≔ ∧ₑ₂ (@lem711940);
opaque symbol lem711942 (n : El num) : Prf (term1 n) ≔ (@lem711941) n;
