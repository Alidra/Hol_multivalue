require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3349929 [_87171 _87182] (f : El (fun _87171 (fun _87182 bool))) (g : El (fun _87171 (fun _87182 bool))) (s : El (fun _87171 bool)) : Prf (⇒ (∀ (λ x : El _87171, (⇒ ((@IN _87171) x s) ((@SUBSET _87182) (f x) (g x))))) ((@SUBSET _87182) ((@UNIONS _87182) ((@IMAGE _87171 (fun _87182 bool)) f s)) ((@UNIONS _87182) ((@IMAGE _87171 (fun _87182 bool)) g s))));
