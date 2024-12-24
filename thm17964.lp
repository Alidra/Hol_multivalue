require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm17964_term_abbrevs;
opaque symbol lem17964 [A] (P : El (fun A bool)) : Prf (= (term0 A P) (= (term1 A P) (term2 A P))) ≔ REFL (term0 A P);
