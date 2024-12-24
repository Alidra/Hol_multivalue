require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3183066_term_abbrevs;
opaque symbol lem3183066 [_83031] (P : El bool) (v : El _83031) (t : El _83031) : Prf (= (term0 _83031 P v t) (= ((@SETSPEC _83031) v P t) (term1 _83031 P v t))) ≔ REFL (term0 _83031 P v t);
