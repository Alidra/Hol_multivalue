require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5738118 [_120327 _120333] : Prf (∀ (λ op : El (fun _120327 (fun _120327 _120327)), (∀ (λ f : El (fun _120333 _120327), (∀ (λ s : El (fun _120333 bool), (= ((@iterate _120327 _120333) op s f) ((@COND _120327) ((@FINITE _120333) ((@support _120333 _120327) op f s)) ((@iterate _120327 _120333) op ((@support _120333 _120327) op f s) f) ((@neutral _120327) op)))))))));
