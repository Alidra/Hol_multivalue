require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2338253_term_abbrevs;
opaque symbol lem2338253 (P : El (fun num bool)) : Prf (= (term0 P) (= (term1 P) (term2 P))) ≔ REFL (term0 P);
