require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.MOD_LT_EQ_term_abbrevs;
require open hol-light.thm163281_spec;
require open hol-light.thm165614_spec;
opaque symbol lem165615 : Prf term0 ≔ EQ_MP (@lem163281) (@lem165614);
