require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm4785471_term_abbrevs;
opaque symbol lem4785471 [A] (h : El A) (t : El (list A)) : Prf (= (term0 A h t) (= (term1 A h t) (term2 A h t))) ≔ REFL (term0 A h t);
