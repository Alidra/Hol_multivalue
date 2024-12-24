require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1240241_term_abbrevs;
require open hol-light.thm1240240_spec;
opaque symbol lem1240241 (char' : El type1335) (_22730' : El type1539) (h1 : Prf (= char' (term0 _22730'))) : Prf (term1 char' _22730') ≔ ∧ₑ₂ (@lem1240240 char' _22730' h1);
