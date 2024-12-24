require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7261450_term_abbrevs;
opaque symbol lem7261450 [_137613] (f : El (fun _137613 real)) (s : El (fun _137613 bool)) (g : El (fun _137613 real)) : Prf (= (term0 _137613 f g s) (term1 _137613 f s g)) ≔ REFL (term0 _137613 f g s);
