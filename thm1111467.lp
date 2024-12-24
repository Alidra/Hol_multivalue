require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1111467_term_abbrevs;
opaque symbol lem1111467 [A] (s : El (fun num A)) (n : El num) : Prf (= (term0 A s n) (= (term1 A s n) (term2 A s n))) ≔ REFL (term0 A s n);
