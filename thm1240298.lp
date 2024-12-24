require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1240298_term_abbrevs;
require open hol-light.thm1240281_spec;
opaque symbol lem1240297 (r : El type1678) : Prf (= r r) ≔ REFL r;
opaque symbol lem1240298 (r : El type1678) (char' : El type1335) (_22730' : El type1539) (h1 : Prf (= _22730' term0)) (h2 : Prf (= char' (term1 _22730'))) : Prf (= (char' r) (term2 r)) ≔ MK_COMB (@lem1240281 char' _22730' h1 h2) (@lem1240297 r);
