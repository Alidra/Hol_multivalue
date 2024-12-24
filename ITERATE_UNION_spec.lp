require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5764203 [_120592 _120607] : Prf (∀ (λ op : El (fun _120607 (fun _120607 _120607)), (⇒ ((@monoidal _120607) op) (∀ (λ f : El (fun _120592 _120607), (∀ (λ s : El (fun _120592 bool), (∀ (λ t : El (fun _120592 bool), (⇒ (∧ ((@FINITE _120592) s) (∧ ((@FINITE _120592) t) ((@DISJOINT _120592) s t))) (= ((@iterate _120607 _120592) op ((@UNION _120592) s t) f) (op ((@iterate _120607 _120592) op s f) ((@iterate _120607 _120592) op t f)))))))))))));
