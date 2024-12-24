require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm322857_term_abbrevs;
opaque symbol lem322857 [A B] (H : El (type549 A B)) (<< : El (type1402 A)) (R : El (type1413 A B)) (h1 : Prf (term0 A B H << R)) : Prf (term0 A B H << R) ≔ h1;
