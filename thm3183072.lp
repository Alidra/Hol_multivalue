require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3183072_term_abbrevs;
opaque symbol lem3183072 [A B] (f : El (fun A B)) (g : El (fun A B)) : Prf (= (term0 A B f g) (= (= f g) (term1 A B f g))) ≔ REFL (term0 A B f g);
