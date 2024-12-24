require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm9233_term_abbrevs;
opaque symbol lem9233 [A B] (t : El (fun A B)) : Prf (= (term0 A B t) (= t (term1 A B t))) ≔ REFL (term0 A B t);
