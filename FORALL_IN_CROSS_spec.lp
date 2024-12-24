require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4334371 [_104099 _104100] : Prf (∀ (λ P : El (fun (prod _104100 _104099) bool), (∀ (λ s : El (fun _104100 bool), (∀ (λ t : El (fun _104099 bool), (= (∀ (λ z : El (prod _104100 _104099), (⇒ ((@IN (prod _104100 _104099)) z ((@CROSS _104099 _104100) s t)) (P z)))) (∀ (λ x : El _104100, (∀ (λ y : El _104099, (⇒ (∧ ((@IN _104100) x s) ((@IN _104099) y t)) (P ((@̦‚ _104100 _104099) x y))))))))))))));
