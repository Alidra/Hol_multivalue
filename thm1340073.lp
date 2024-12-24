require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1340073_term_abbrevs;
require open hol-light.TREAL_INV_0_spec;
require open hol-light.thm1340072_spec;
opaque symbol lem1340073 : Prf (= term0 term1) ≔ EQ_MP (@lem1340072) (@lem1331743);
