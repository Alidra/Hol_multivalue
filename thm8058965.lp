require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm8058965_term_abbrevs;
opaque symbol lem8058965 [_143118 _143154 _143158 _143159] (h : El (type1644 _143118 _143154 _143158 _143159)) (t : El (type1633 _143118 _143154 _143158 _143159)) (f : El _143159) (x : El _143158) : Prf (= (term0 _143118 _143154 _143158 _143159 h t f x) (= (term1 _143118 _143154 _143158 _143159 h t f x) (term2 _143118 _143154 _143158 _143159 h t f x))) ≔ REFL (term0 _143118 _143154 _143158 _143159 h t f x);
