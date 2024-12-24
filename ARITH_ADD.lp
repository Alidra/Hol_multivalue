require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.ARITH_ADD_term_abbrevs;
require open hol-light.thm513870_spec;
require open hol-light.thm514290_spec;
opaque symbol lem514291 : Prf term0 ≔ EQ_MP (@lem513870) (@lem514290);
