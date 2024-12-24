require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3655226 [_93490 _93497] : Prf (∀ (λ P : El (fun (fun _93497 bool) bool), (∀ (λ f : El (fun _93490 _93497), (∀ (λ s : El (fun _93490 bool), (= (∃ (λ t : El (fun _93497 bool), (∧ ((@SUBSET _93497) t ((@IMAGE _93490 _93497) f s)) (P t)))) (∃ (λ t : El (fun _93490 bool), (∧ ((@SUBSET _93490) t s) (∧ (∀ (λ x : El _93490, (∀ (λ y : El _93490, (⇒ (∧ ((@IN _93490) x t) ((@IN _93490) y t)) (= (= (f x) (f y)) (= x y))))))) (P ((@IMAGE _93490 _93497) f t)))))))))))));
