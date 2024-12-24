require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1098348_term_abbrevs;
opaque symbol lem1098348 [A] (h : El A) (t : El (list A)) : Prf (= (term0 A h t) (= (term1 A h t) (term2 A h t))) ≔ REFL (term0 A h t);
