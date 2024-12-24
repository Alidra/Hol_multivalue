require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1069370_term_abbrevs;
require open hol-light.thm1069367_spec;
opaque symbol lem1069370 [A] (option' : El (type1338 A)) (NONE' : El (recspace A)) (SOME' : El (type1432 A)) (h1 : Prf (= option' (term0 A NONE' SOME'))) : Prf (option' NONE') ≔ ∧ₑ₁ (@lem1069367 A option' NONE' SOME' h1);
