require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3211657_term_abbrevs;
opaque symbol lem3211657 [A B] (y : El B) (f : El (fun A B)) (s : El (fun A bool)) : Prf (= (term0 A B y s f) (= (term1 A B y f s) (term2 A B y f s))) ≔ REFL (term0 A B y s f);
