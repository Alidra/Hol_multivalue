require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4374857 [_104907 _104908] (f : El (fun (fun _104907 bool) bool)) (g : El (fun (fun _104908 bool) bool)) (h1 : Prf (¬ (= f (@EMPTY (fun _104907 bool))))) (h2 : Prf (= g (@EMPTY (fun _104908 bool)))) : Prf (∀ (λ p1 : El _104907, (∀ (λ p2 : El _104908, (= (∧ ((@IN _104907) p1 ((@INTERS _104907) f)) ((@IN _104908) p2 ((@INTERS _104908) (@EMPTY (fun _104908 bool))))) (∀ (λ s : El (fun _104907 bool), (⇒ ((@IN (fun _104907 bool)) s f) (∧ ((@IN _104907) p1 s) ((@IN _104908) p2 (@UNIV _104908)))))))))));
