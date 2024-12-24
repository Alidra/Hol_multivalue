require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4417723 [_106189 _106193] : Prf (∀ (λ k : El (fun _106193 bool), (∀ (λ s : El (fun _106193 (fun _106189 bool)), (∀ (λ x : El (fun _106193 _106189), (∀ (λ y : El (fun _106193 _106189), (⇒ (∧ ((@IN (fun _106193 _106189)) x ((@cartesian_product _106189 _106193) k s)) ((@IN (fun _106193 _106189)) y ((@cartesian_product _106189 _106193) k s))) (= (= x y) (∀ (λ i : El _106193, (⇒ ((@IN _106193) i k) (= (x i) (y i)))))))))))))));
