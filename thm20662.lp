require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm20662_term_abbrevs;
opaque symbol lem20662 [A B] (f : El (fun A B)) (x : El A) : Prf (= (term0 A B f x) (= (f x) ((@I (fun A B)) f x))) ≔ REFL (term0 A B f x);
