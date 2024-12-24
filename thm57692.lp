require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm57692_term_abbrevs;
opaque symbol lem57692 [A B] (f : El (fun A B)) (x : El A) : Prf (= (term0 A B f x) (= ((@LET A B) f x) (f x))) ≔ REFL (term0 A B f x);
