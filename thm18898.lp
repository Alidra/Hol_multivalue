require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm18898_term_abbrevs;
require open hol-light.SKOLEM_THM_spec;
opaque symbol lem18898 [A B] (P : El (type1413 A B)) : Prf (term0 A B P) ≔ (@lem13546 A B) P;
