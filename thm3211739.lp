require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3211739_term_abbrevs;
opaque symbol lem3211739 [A] (s : El (fun A bool)) (t : El (fun A bool)) : Prf (= (term0 A s t) (= ((@DISJOINT A) s t) (= ((@INTER A) s t) (@EMPTY A)))) ≔ REFL (term0 A s t);
