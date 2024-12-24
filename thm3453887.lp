require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3453887_term_abbrevs;
opaque symbol lem3453887 [_83095] (p : El (fun _83095 bool)) (x : El _83095) : Prf (= (term0 _83095 p x) (= (term1 _83095 x p) (p x))) ≔ REFL (term0 _83095 p x);
