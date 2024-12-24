require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1110682_term_abbrevs;
opaque symbol lem1110682 [A] (h : El A) (r : El (type1402 A)) (t : El (list A)) : Prf (= (term0 A h r t) (= (term1 A r h t) (term2 A h r t))) ≔ REFL (term0 A h r t);
