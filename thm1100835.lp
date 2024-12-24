require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1100835_term_abbrevs;
opaque symbol lem1100835 [_25307] (P : El (fun _25307 bool)) : Prf (= (term0 _25307 P) (= ((@ALL _25307) P (@NIL _25307)) T)) ≔ REFL (term0 _25307 P);
