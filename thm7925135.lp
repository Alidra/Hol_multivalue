require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7925135_term_abbrevs;
require open hol-light.thm7925118_spec;
opaque symbol lem7925134 [A] (r : El (type1676 A)) : Prf (= r r) ≔ REFL r;
opaque symbol lem7925135 [A] (r : El (type1676 A)) (tybit0' : El (type1331 A)) (_103783' : El (type45 A)) (h1 : Prf (= _103783' (term0 A))) (h2 : Prf (= tybit0' (term1 A _103783'))) : Prf (= (tybit0' r) (term2 A r)) ≔ MK_COMB (@lem7925118 A tybit0' _103783' h1 h2) (@lem7925134 A r);
