require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4373533 [_104960 _104961] (s : El (fun _104960 bool)) (f : El (fun (fun _104961 bool) bool)) (h1 : Prf (= f (@EMPTY (fun _104961 bool)))) : Prf (= (∀ (λ p1 : El _104960, (∀ (λ p2 : El _104961, (= (∧ ((@IN _104960) p1 s) ((@IN _104961) p2 ((@INTERS _104961) (@EMPTY (fun _104961 bool))))) (∧ ((@IN _104960) p1 s) ((@IN _104961) p2 (@UNIV _104961)))))))) (= ((@CROSS _104961 _104960) s ((@INTERS _104961) f)) ((@CROSS _104961 _104960) s (@UNIV _104961))));
