require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem51887 [_5106 _5107] (P : El (fun (prod _5107 _5106) bool)) : Prf (= ((λ P' : El (fun (prod _5107 _5106) bool), (= (∀ (λ p : El (prod _5107 _5106), (P' p))) (∀ (λ p1 : El _5107, (∀ (λ p2 : El _5106, (P' ((@̦‚ _5107 _5106) p1 p2)))))))) P) (= (∀ (λ p : El (prod _5107 _5106), (P p))) (∀ (λ p1 : El _5107, (∀ (λ p2 : El _5106, (P ((@̦‚ _5107 _5106) p1 p2))))))));
