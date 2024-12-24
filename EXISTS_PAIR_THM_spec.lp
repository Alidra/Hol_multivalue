require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem51006 [_5131 _5132] : Prf (∀ (λ P : El (fun (prod _5132 _5131) bool), (= (∃ (λ p : El (prod _5132 _5131), (P p))) (∃ (λ p1 : El _5132, (∃ (λ p2 : El _5131, (P ((@̦‚ _5132 _5131) p1 p2)))))))));
