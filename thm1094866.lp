require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1094866_term_abbrevs;
opaque symbol lem1094866 [A] (t : El (list A)) (h : El A) : Prf (= (term0 A t h) (= (term1 A h t) h)) ≔ REFL (term0 A t h);
