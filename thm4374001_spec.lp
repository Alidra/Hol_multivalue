require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4374001 [_105011 _105012] (t : El (fun _105012 bool)) (f : El (fun (fun _105011 bool) bool)) (h1 : Prf (= f (@EMPTY (fun _105011 bool)))) : Prf (= (∀ (λ p1 : El _105011, (∀ (λ p2 : El _105012, (= (∧ ((@IN _105011) p1 ((@INTERS _105011) (@EMPTY (fun _105011 bool)))) ((@IN _105012) p2 t)) (∧ ((@IN _105011) p1 (@UNIV _105011)) ((@IN _105012) p2 t))))))) (= ((@CROSS _105012 _105011) ((@INTERS _105011) f) t) ((@CROSS _105012 _105011) (@UNIV _105011) t)));
