require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5737458 [_120222 _120250] : Prf (∀ (λ op : El (fun _120222 (fun _120222 _120222)), (∀ (λ s : El (fun _120250 bool), (∀ (λ f : El (fun _120250 _120222), (∀ (λ a : El _120250, (= ((@support _120250 _120222) op (λ x : El _120250, ((@COND _120222) (= x a) (f x) ((@neutral _120222) op))) s) ((@COND (fun _120250 bool)) ((@IN _120250) a s) ((@support _120250 _120222) op f ((@INSERT _120250) a (@EMPTY _120250))) (@EMPTY _120250)))))))))));
