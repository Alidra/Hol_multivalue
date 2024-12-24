require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7637147_term_abbrevs;
opaque symbol lem7637147 [A] (s : El (fun A bool)) : Prf (= (term0 A s) (= ((@dimindex A) s) ((@dimindex A) (@UNIV A)))) ≔ REFL (term0 A s);
