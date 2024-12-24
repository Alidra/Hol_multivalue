require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1111461_term_abbrevs;
opaque symbol lem1111461 [A] (s : El (fun num A)) : Prf (= (term0 A s) (= (term1 A s) (@NIL A))) ≔ REFL (term0 A s);
