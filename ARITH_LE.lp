require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.ARITH_LE_term_abbrevs;
require open hol-light.thm517422_spec;
require open hol-light.thm519779_spec;
opaque symbol lem519780 : Prf term0 ≔ EQ_MP (@lem517422) (@lem519779);
