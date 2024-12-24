require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm11005_term_abbrevs;
require open hol-light.thm32_spec;
opaque symbol lem11005 (P : El (fun bool bool)) : Prf (= (term0 P) (= (term1 P) (term2 P))) ≔ (@lem32 (term1 P) (term2 P));
