require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7260963_term_abbrevs;
opaque symbol lem7260963 (a : El num) (b : El num) (f : El (fun num real)) (g : El (fun num real)) (h1 : Prf (term0 a b f g)) : Prf (term0 a b f g) ≔ h1;
