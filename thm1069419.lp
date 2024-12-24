require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1069419_term_abbrevs;
require open hol-light.thm1069398_spec;
opaque symbol lem1069418 [A] (r : El (recspace A)) : Prf (= r r) ≔ REFL r;
opaque symbol lem1069419 [A] (r : El (recspace A)) (option' : El (type1338 A)) (SOME' : El (type1432 A)) (NONE' : El (recspace A)) (h1 : Prf (= SOME' (term0 A))) (h2 : Prf (= option' (term1 A NONE' SOME'))) (h3 : Prf (= NONE' (term2 A))) : Prf (= (option' r) (term3 A r)) ≔ MK_COMB (@lem1069398 A option' SOME' NONE' h1 h2 h3) (@lem1069418 A r);
