require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1100844_term_abbrevs;
opaque symbol lem1100844 [_25307] (h : El _25307) (P : El (fun _25307 bool)) (t : El (list _25307)) : Prf (= (term0 _25307 h P t) (= (term1 _25307 P h t) (term2 _25307 h P t))) ≔ REFL (term0 _25307 h P t);
