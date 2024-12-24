require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3791011_term_abbrevs;
require open hol-light.thm3791009_spec;
require open hol-light.thm3791010_spec;
opaque symbol lem3791011 [A B] (f : El (type1411 A B)) (s : El (fun A bool)) (a : El B) (b : El B) : Prf (= (term0 A B f b s a) (term1 A B s a b)) ≔ EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b);
