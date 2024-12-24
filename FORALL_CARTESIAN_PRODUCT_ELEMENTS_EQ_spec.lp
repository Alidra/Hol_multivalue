require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4452626 [_106843 _106845] : Prf (∀ (λ P : El (fun _106845 (fun _106843 bool)), (∀ (λ k : El (fun _106845 bool), (∀ (λ s : El (fun _106845 (fun _106843 bool)), (⇒ (¬ (= ((@cartesian_product _106843 _106845) k s) (@EMPTY (fun _106845 _106843)))) (= (∀ (λ i : El _106845, (∀ (λ x : El _106843, (⇒ (∧ ((@IN _106845) i k) ((@IN _106843) x (s i))) (P i x)))))) (∀ (λ z : El (fun _106845 _106843), (∀ (λ i : El _106845, (⇒ (∧ ((@IN (fun _106845 _106843)) z ((@cartesian_product _106843 _106845) k s)) ((@IN _106845) i k)) (P i (z i)))))))))))))));
