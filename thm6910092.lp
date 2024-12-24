require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm6910092_term_abbrevs;
opaque symbol lem6910092 [A] (P : El (fun A bool)) (x : El A) : Prf (= (term0 A P x) (term1 A P x)) ≔ REFL (term0 A P x);
