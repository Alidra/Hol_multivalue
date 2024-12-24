require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7931515_term_abbrevs;
opaque symbol lem7931515 [A B] (f : El (fun A B)) (s : El (fun A bool)) (n : El num) : Prf (= (term0 A B f s n) (term1 A B f s n)) ≔ REFL (term0 A B f s n);
