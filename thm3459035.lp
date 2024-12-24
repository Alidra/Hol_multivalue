require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3459035_term_abbrevs;
opaque symbol lem3459035 [A] (s : El (fun A bool)) (t : El (fun A bool)) : Prf (= (term0 A s t) (= (= s t) (term1 A s t))) ≔ REFL (term0 A s t);
