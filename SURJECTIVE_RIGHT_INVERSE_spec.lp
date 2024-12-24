require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3576206 [_91560 _91563] (f : El (fun _91563 _91560)) : Prf (= (∀ (λ y : El _91560, (∃ (λ x : El _91563, (= (f x) y))))) (∃ (λ g : El (fun _91560 _91563), (∀ (λ y : El _91560, (= (f (g y)) y))))));
