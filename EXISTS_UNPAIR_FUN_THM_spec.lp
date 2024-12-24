require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem55166 [_5658 _5667 _5668] : Prf (∀ (λ P : El (fun (fun _5658 _5667) (fun (fun _5658 _5668) bool)), (= (∃ (λ f : El (fun _5658 _5667), (∃ (λ g : El (fun _5658 _5668), (P f g))))) (∃ (λ h : El (fun _5658 (prod _5667 _5668)), (P ((@o _5658 (prod _5667 _5668) _5667) (@FST _5667 _5668) h) ((@o _5658 (prod _5667 _5668) _5668) (@SND _5667 _5668) h)))))));
