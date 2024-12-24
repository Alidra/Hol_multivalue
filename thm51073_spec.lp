require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem51073 [_5146 _5153 _5154] (t : El (fun (prod _5154 _5153) _5146)) (p1 : El _5154) (p2 : El _5153) : Prf (= ((@= _5146) ((λ p : El (prod _5154 _5153), (t p)) ((@̦‚ _5154 _5153) p1 p2))) ((@= _5146) (t ((@̦‚ _5154 _5153) p1 p2))));
