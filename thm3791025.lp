require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3791025_term_abbrevs;
opaque symbol lem3791025 [A B] (b : El B) (s : El (fun A bool)) (n : El num) (a : El B) (f : El (type1411 A B)) : Prf (= (term0 A B b s n a f) (= (term1 A B f b s a n) (term2 A B b s n a f))) ≔ REFL (term0 A B b s n a f);
