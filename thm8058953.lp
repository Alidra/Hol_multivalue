require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm8058953_term_abbrevs;
opaque symbol lem8058953 [_143118 _143154 _143158 _143159] (f : El _143159) (x : El _143158) : Prf (= (term0 _143118 _143154 _143158 _143159 f x) (= ((@CASEWISE _143118 _143154 _143158 _143159) (@NIL (prod (fun _143154 _143158) (fun _143159 (fun _143154 _143118)))) f x) (term1 _143118))) ≔ REFL (term0 _143118 _143154 _143158 _143159 f x);
