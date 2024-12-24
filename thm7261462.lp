require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7261462_term_abbrevs;
opaque symbol lem7261462 (f : El (fun num real)) (a : El num) (b : El num) (g : El (fun num real)) : Prf (= (term0 f a g b) (term1 f a b g)) ≔ REFL (term0 f a g b);
