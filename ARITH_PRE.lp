require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.ARITH_PRE_term_abbrevs;
require open hol-light.thm513386_spec;
require open hol-light.thm513549_spec;
opaque symbol lem513550 : Prf term0 ≔ EQ_MP (@lem513386) (@lem513549);
