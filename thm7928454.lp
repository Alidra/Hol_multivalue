require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7928454_term_abbrevs;
require open hol-light.thm7928437_spec;
opaque symbol lem7928453 [A] (r : El (type1675 A)) : Prf (= r r) ≔ REFL r;
opaque symbol lem7928454 [A] (r : El (type1675 A)) (tybit1' : El (type1329 A)) (_103802' : El (type39 A)) (h1 : Prf (= _103802' (term0 A))) (h2 : Prf (= tybit1' (term1 A _103802'))) : Prf (= (tybit1' r) (term2 A r)) ≔ MK_COMB (@lem7928437 A tybit1' _103802' h1 h2) (@lem7928453 A r);
