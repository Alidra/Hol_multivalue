require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1164040 [_27380 _27381 _27382 _27383] (P : El (fun _27381 (fun _27380 bool))) (f : El (fun _27382 _27381)) (g : El (fun _27383 _27380)) : Prf (∀ (λ l : El (list _27382), (∀ (λ m : El (list _27383), (= ((@ALL2 _27381 _27380) P ((@MAP _27382 _27381) f l) ((@MAP _27383 _27380) g m)) ((@ALL2 _27382 _27383) (λ x : El _27382, (λ y : El _27383, (P (f x) (g y)))) l m))))));
