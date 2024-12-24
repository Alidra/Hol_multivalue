require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm16265_term_abbrevs;
require open hol-light.thm32_spec;
opaque symbol lem16265 (P : El (fun 1 bool)) : Prf (= (term0 P) (= (term1 P) (P one))) ≔ (@lem32 (term1 P) (P one));
