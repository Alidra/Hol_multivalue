require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm16452_term_abbrevs;
opaque symbol lem16452 [A] (P : El (fun A bool)) (Q : El (fun A bool)) : Prf (= (term0 A P Q) (= (term1 A P Q) (term2 A P Q))) ≔ REFL (term0 A P Q);
