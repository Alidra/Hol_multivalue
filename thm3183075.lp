require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3183075_term_abbrevs;
opaque symbol lem3183075 [A] (p : El (fun A bool)) : Prf (= (term0 A p) (= ((@GSPEC A) p) p)) ≔ REFL (term0 A p);
