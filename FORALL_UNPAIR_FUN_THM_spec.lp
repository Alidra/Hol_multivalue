require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem54977 [_5621 _5630 _5631] : Prf (∀ (λ P : El (fun (fun _5621 _5630) (fun (fun _5621 _5631) bool)), (= (∀ (λ f : El (fun _5621 _5630), (∀ (λ g : El (fun _5621 _5631), (P f g))))) (∀ (λ h : El (fun _5621 (prod _5630 _5631)), (P ((@o _5621 (prod _5630 _5631) _5630) (@FST _5630 _5631) h) ((@o _5621 (prod _5630 _5631) _5631) (@SND _5630 _5631) h)))))));
