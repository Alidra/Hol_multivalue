require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1101597_term_abbrevs;
opaque symbol lem1101597 [_25328] (h : El _25328) (P : El (fun _25328 bool)) (t : El (list _25328)) : Prf (= (term0 _25328 h P t) (= (term1 _25328 P h t) (term2 _25328 h P t))) ≔ REFL (term0 _25328 h P t);
