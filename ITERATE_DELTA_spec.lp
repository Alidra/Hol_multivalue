require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5825973 [_121513 _121532] : Prf (∀ (λ op : El (fun _121513 (fun _121513 _121513)), (⇒ ((@monoidal _121513) op) (∀ (λ f : El (fun _121532 _121513), (∀ (λ a : El _121532, (∀ (λ s : El (fun _121532 bool), (= ((@iterate _121513 _121532) op s (λ x : El _121532, ((@COND _121513) (= x a) (f x) ((@neutral _121513) op)))) ((@COND _121513) ((@IN _121532) a s) (f a) ((@neutral _121513) op))))))))))));
