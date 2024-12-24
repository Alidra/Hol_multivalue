require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1110673_term_abbrevs;
opaque symbol lem1110673 [A] (r : El (type1402 A)) : Prf (= (term0 A r) (= ((@PAIRWISE A) r (@NIL A)) T)) ≔ REFL (term0 A r);
